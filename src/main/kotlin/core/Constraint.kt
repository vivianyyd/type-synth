package core

import query.App
import query.Example
import query.Name
import util.Counter

sealed interface ConstraintType<L : Language>
sealed class CTypeConstructor<L : Language>(open val params: MutableList<ConstraintType<L>>) : ConstraintType<L> {
    abstract fun match(other: CTypeConstructor<L>): Boolean
    fun split(other: CTypeConstructor<L>): List<Constraint<L>>? =
        if (match(other)) params.zip(other.params).map { (a, b) -> EqualityConstraint(a, b) } else null
}

sealed interface CVariable<L : Language> : ConstraintType<L>
sealed interface Substitutable  // : CVariable?

data class CArrow<L : Language> private constructor(override val params: MutableList<ConstraintType<L>>) :
    CTypeConstructor<L>(params) {
    constructor(l: ConstraintType<L>, r: ConstraintType<L>) : this(mutableListOf(l, r))

    override fun match(other: CTypeConstructor<L>) = other is CArrow<L>
}

data class Instantiation<L : Language>(val n: SearchNode<L>, val id: Int) : CVariable<L>
data class ProofVariable<L : Language>(val id: Int) : CVariable<L>, Substitutable

sealed interface Constraint<L : Language>
data class EqualityConstraint<L : Language>(val l: ConstraintType<L>, val r: ConstraintType<L>) : Constraint<L>

class Unification<L : Language>(state: SearchState<L>, exs: List<Example>) {
    private val constraints = mutableListOf<Constraint<L>>()
    private var instId = Counter()
    private var proofVarId = Counter()

    init {
        fun constrainType(ex: Example): ConstraintType<L> = when (ex) {
            is Name -> state.searchNodeOf(ex.name).instantiate(instId)
            is App -> {
                val proofVariable = ProofVariable<L>(proofVarId.get())
                constraints.add(EqualityConstraint(constrainType(ex.fn), CArrow(constrainType(ex.arg), proofVariable)))
                proofVariable
            }
        }

        exs.forEach { constrainType(it) }
        TODO(
            "Do we need to call constraints from examples for each layer? " +
                    "i.e. will lineups lose information we need?" +
                    "or can we make each new rounds of constraints based on the simplified older ones"
        )
    }

    /** Precondition: constraints are simplified.
     * This function does not simplify constraints */
    fun commit(instantiationsToCommitments: List<Pair<Instantiation<L>, ConstraintType<L>>>): Boolean =
        instantiationsToCommitments.fold(false) { changed, (inst, ty) ->
            var changedCurr = changed
            for (j in constraints.indices) {
                if (constraints[j] is EqualityConstraint<L>) {
                    val constr = constraints[j] as EqualityConstraint<L>
                    val newL = if (constr.l == inst) ty else constr.l
                    val newR = if (constr.r == inst) ty else constr.r
                    constraints[j] = EqualityConstraint(newL, newR)
                    changedCurr = changedCurr || constr.l == inst || constr.r == inst
                }
            }
            changedCurr
        }

    fun simplify() {
        while (substs() || splits()) {
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
        }

    private fun substs(): Boolean {
        val eqs = constraints.filterIsInstance<EqualityConstraint<L>>()
        for (eq in eqs) {
            if (eq.l is Substitutable || eq.r is Substitutable) {
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
        }
        return constraints.removeAll { it in eqs }
    }

    private fun splits(): Boolean {
        var success = true
        val newConstrs = mutableListOf<Constraint<L>>()
        fun splittable(c: Constraint<L>) =
            c is EqualityConstraint<L> && c.l is CTypeConstructor<L> && c.r is CTypeConstructor<L>
        for (constr in constraints.filter { splittable(it) }.filterIsInstance<EqualityConstraint<L>>()) {
            val result = (constr.l as CTypeConstructor<L>).split(constr.r as CTypeConstructor<L>)
            if (result == null) {
                success = false
                break
            }
            newConstrs.addAll(result)
        }
        if (!success) TODO()
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
