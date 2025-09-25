package core

import query.App
import query.Example
import query.Name
import util.Counter

sealed interface ConstraintType<L : Language>
sealed class CTypeConstructor<L : Language>(open val params: MutableList<ConstraintType<L>>) : ConstraintType<L> {
    abstract fun match(other: CTypeConstructor<L>): Boolean
    open fun split(other: CTypeConstructor<L>): List<Constraint<L>>? =
        if (match(other)) params.zip(other.params).map { (a, b) -> EqualityConstraint(a, b) } else null
}

sealed interface CVariable<L : Language> : ConstraintType<L>
sealed interface Substitutable  // : CVariable?

data class CArrow<L : Language> private constructor(override val params: MutableList<ConstraintType<L>>) :
    CTypeConstructor<L>(params) {
    constructor(l: ConstraintType<L>, r: ConstraintType<L>) : this(mutableListOf(l, r))

    override fun match(other: CTypeConstructor<L>) = other is CArrow<L>

    override fun toString() = "${if (params[0] is CArrow) "(${params[0]})" else "${params[0]}"} -> ${params[1]}"
}

data class Instantiation<L : Language>(val n: SearchNode<L>, val id: Int) : CVariable<L> {
    override fun toString() = "inst$id"
}

data class ProofVariable<L : Language>(val id: Int) : CVariable<L>, Substitutable {
    override fun toString() = "T$id"
}

sealed interface Constraint<L : Language>
data class EqualityConstraint<L : Language>(val l: ConstraintType<L>, val r: ConstraintType<L>) : Constraint<L> {
    override fun toString() = "$l = $r"
}

class Unification<L : Language>(candidate: Candidate<L>, exs: List<Example>) {
    private val constraints = mutableListOf<Constraint<L>>()
    private var instVarId = Counter()
    private var proofVarId = Counter()
    private var error = false
    private var insts = Counter()  // Number of times any top-level type has been instantiated

    init {
        fun constrainType(ex: Example): ConstraintType<L> = when (ex) {
            is Name -> candidate.searchNodeOf(ex.name).instantiate(instVarId, insts.get())
            is App -> {
                val proofVariable = ProofVariable<L>(proofVarId.get())
                constraints.add(EqualityConstraint(constrainType(ex.fn), CArrow(constrainType(ex.arg), proofVariable)))
                proofVariable
            }
        }
        exs.forEach { constrainType(it) }

        simplify()
    }

    fun get(): List<Constraint<L>>? = if (error) null else constraints

//    /** Precondition: constraints are simplified.
//     * @return [true] if the commitment produces no errors.
//     * Micro-opt later: Don't bother committing if running commit with those changes doesn't do anything */
//    fun commit(instantiationsToCommitments: List<Pair<Instantiation<L>, ConstraintType<L>>>): Boolean {
//        val change = instantiationsToCommitments.fold(false) { changed, (inst, ty) ->
//            var changedCurr = changed
//            for (j in constraints.indices) {
//                if (constraints[j] is EqualityConstraint<L>) {
//                    val constr = constraints[j] as EqualityConstraint<L>
//                    val newL = if (constr.l == inst) ty else constr.l
//                    val newR = if (constr.r == inst) ty else constr.r
//                    constraints[j] = EqualityConstraint(newL, newR)
//                    changedCurr = changedCurr || constr.l == inst || constr.r == inst
//                }
//            }
//            changedCurr
//        }
//        simplify()
//        return !error
//    }

    fun simplify() {
        while (substs() || splits()) {
            constraints.removeAll { it is EqualityConstraint && it.l == it.r }
//            println(constraints.joinToString(separator = "\n", postfix = "\n============="))
        }
    }

    /** Replace [v] with [s] in [t] inplace. */
    private fun substitute(v: Substitutable, s: ConstraintType<L>, t: ConstraintType<L>): ConstraintType<L> =
        when (t) {
            is Substitutable -> if (t == v) s else t
            is Instantiation -> t
            is CTypeConstructor -> {
                t.params.replaceAll { substitute(v, s, it) }
                t
            }

            is InitConstrV -> t
        }

    private fun substs(): Boolean {
        val eqs = constraints.filterIsInstance<EqualityConstraint<L>>()
            .filter { it.l is Substitutable || it.r is Substitutable }
        for (eq in eqs) {
            val v: Substitutable = if (eq.l is Substitutable) eq.l else (eq.r as Substitutable)
            val s = if (eq.l is Substitutable) eq.r else eq.l
            for (j in constraints.indices) {
                if (constraints[j] is EqualityConstraint<L>) {
                    constraints[j] = EqualityConstraint(
                        substitute(v, s, (constraints[j] as EqualityConstraint<L>).l),
                        substitute(v, s, (constraints[j] as EqualityConstraint<L>).r)
                    )
                }
            }
        }
        return constraints.removeAll { it in eqs }
    }

    private fun splits(): Boolean {
        val newConstrs = mutableListOf<Constraint<L>>()
        fun splittable(c: Constraint<L>) =
            c is EqualityConstraint<L> && c.l is CTypeConstructor<L> && c.r is CTypeConstructor<L>
        for (constr in constraints.filter { splittable(it) }.filterIsInstance<EqualityConstraint<L>>()) {
            val result = (constr.l as CTypeConstructor<L>).split(constr.r as CTypeConstructor<L>)
            if (result == null) {
                error = true
                break
            }
            newConstrs.addAll(result)
        }
        if (error) return false
        val changed = constraints.removeAll { splittable(it) }
        constraints.addAll(newConstrs)
        return changed
    }
}

//object CInitVar : CVariable<Init>

//TODO(
//"Need to also form label equivalence classes for middle abstraction. " +
//"Need state that L can modify / make Constraint an interface and have middle abstraction" +
//"implement new constraint that forces label names to be the same"
//)

/*
Handling conflicts:
- conflict analysis - small set of assignments in DAG that separates conflict from roots (cut)
- two literal watching - only check clauses for which the variable set is one of the two that is being watched
    I think we cannot really do this but maybe it's not so bad bc each constraint has at most two inst() nodes
 */
