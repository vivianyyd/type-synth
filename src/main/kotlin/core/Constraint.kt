package core

import query.App
import query.Example
import query.Name
import test.ConsTest
import util.Counter

/** ConstraintTypes are mutable */
sealed interface ConstraintType<L : Language> {
    fun substitutable(): List<Substitutable<L>>
}

sealed class CTypeConstructor<L : Language>(open val params: MutableList<ConstraintType<L>>) : ConstraintType<L> {
    override fun substitutable(): List<Substitutable<L>> = params.flatMap { it.substitutable() }
    abstract fun match(other: CTypeConstructor<L>): Boolean
    open fun split(other: CTypeConstructor<L>): List<Constraint<L>>? =
        if (match(other)) params.zip(other.params).map { (a, b) -> EqualityConstraint(a, b) } else null
}

sealed interface CVariable<L : Language> : ConstraintType<L> {
    override fun substitutable(): List<Substitutable<L>> = listOf()
}

sealed interface Substitutable<L : Language> : CVariable<L> {
    override fun substitutable(): List<Substitutable<L>> = listOf(this)
}

data class CArrow<L : Language> private constructor(override val params: MutableList<ConstraintType<L>>) :
    CTypeConstructor<L>(params) {
    constructor(l: ConstraintType<L>, r: ConstraintType<L>) : this(mutableListOf(l, r))

    override fun match(other: CTypeConstructor<L>) = other is CArrow<L>

    override fun toString() = "${if (params[0] is CArrow) "(${params[0]})" else "${params[0]}"} -> ${params[1]}"
}

/**
 * It is this class's job to instantiate its children once a commitment is made.
 * inst denotes _which_ instantiation we are in. This matters bc if we fill a hole with a variable,
 * that variable needs to know where it is so it matches the others in the same instantiation call. */
data class Instantiation<L : Language>(val n: Hole<L>, val uniqueId: Int, val inst: Int, val freshIdGen: Counter) :
    CVariable<L> {  // Not substitutable - we need these to induce choices, can't discard as we do when we substitute
    override fun toString() = "inst$uniqueId-$inst"
}

data class ProofVariable<L : Language>(val id: Int) : CVariable<L>, Substitutable<L> {
    override fun toString() = "T$id"
}

sealed interface Constraint<L : Language> {
    fun trivial(): Boolean
}

data class EqualityConstraint<L : Language>(var l: ConstraintType<L>, var r: ConstraintType<L>) : Constraint<L> {
    override fun toString() = "$l = $r"
    override fun trivial() = l == r || l is InitConstrV || r is InitConstrV
    fun substitutable() = l.substitutable() + r.substitutable()
}

typealias Commitment<L> = Pair<Hole<L>, SearchNode<L>>?

class Unification<L : Language> {
    private val constraints = mutableListOf<Constraint<L>>()
    private var instVarId = Counter()
    private var proofVarId = Counter()
    private var error = false
    private var insts = Counter()  // Number of times any top-level type has been instantiated
    private val references = mutableMapOf<Substitutable<L>, MutableSet<EqualityConstraint<L>>>()

    constructor(constraints: List<Constraint<L>>) {
        this.constraints.addAll(constraints)
        constraints.filterIsInstance<EqualityConstraint<L>>().forEach { addReferences(it) }
    }

    constructor(candidate: Candidate<L>, exs: List<Example>) : this(listOf()) {
        fun constrainType(ex: Example): ConstraintType<L> = when (ex) {
            is Name -> candidate.searchNodeOf(ex.name).instantiate(instVarId, insts.get())
            is App -> {
                val proofVariable = ProofVariable<L>(proofVarId.get())
                val c = EqualityConstraint(constrainType(ex.fn), CArrow(constrainType(ex.arg), proofVariable))
                addReferences(c)
                constraints.add(c)
                proofVariable
            }
        }
        exs.forEach { constrainType(it) }

        simplify()
    }

    fun get(): List<Constraint<L>>? = if (error) null else constraints

    private fun addReferences(c: EqualityConstraint<L>) {
        val substitutables = c.substitutable()
        substitutables.forEach {
            references.getOrPut(it) { mutableSetOf() }.add(c)
        }
    }

    private fun removeReferences(c: EqualityConstraint<L>) {
        val substitutables = c.substitutable()
        substitutables.forEach {
            references[it]!!.remove(c)
        }
    }

    fun commitAndCheckValid(refinements: List<Pair<Hole<L>, SearchNode<L>>>): Boolean {
        betterCommit(refinements)
        return !error
    }

    /**
    Optimization: Don't bother committing if running commit with those changes doesn't do anything.
    e.g. If we refine a hole to a fresh variable, store a list of commitments that we are delaying until later
     */
    private fun betterCommit(refinements: List<Pair<Hole<L>, SearchNode<L>>>): Boolean {
        val change = refinements.fold(false) { changed, (hole, node) ->
            var changedCurr = changed
            for (j in constraints.indices) {
                if (constraints[j] is EqualityConstraint<L>) {
                    val constr = constraints[j] as EqualityConstraint<L>

                    fun newGuy(n: ConstraintType<L>) =
                        if (n is Instantiation && n in hole.instantiations())
                            node.instantiate(
                                n.freshIdGen,
                                n.inst
                            ) else n

                    val newL = newGuy(constr.l)
                    val newR = newGuy(constr.r)
                    val newC = EqualityConstraint(newL, newR)
                    constraints[j] = newC
                    removeReferences(constr)
                    addReferences(newC)
                    changedCurr = changedCurr || constr.l != newL || constr.r != newR
                }
            }
            changedCurr
        }
        simplify()
        return change
    }

    private fun simplify() {
        fun trivial() {
            constraints.removeAll {
                val t = it.trivial()
                if (t && it is EqualityConstraint<L>) removeReferences(it)
                t
            }
        }

        var substChange = substs()
        var splitChange = splits()
        while (splitChange || substChange) {
            val cset = constraints.toSet()
            constraints.clear()
            constraints.addAll(cset)
            substChange = if (splitChange) substs() else false
            splitChange = splits()
            trivial()
        }
        trivial()
        val cset = constraints.toSet()
        constraints.clear()
        constraints.addAll(cset)
    }

    /** Replace [v] with [s] in [t] inplace. */
    private fun substitute(v: Substitutable<L>, s: ConstraintType<L>, t: ConstraintType<L>): ConstraintType<L> =
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
        val substs = constraints.filterIsInstance<EqualityConstraint<L>>()
            .filter { it.l is Substitutable || it.r is Substitutable }.map { eq ->
                val v: Substitutable<L> =
                    if (eq.l is ProofVariable) eq.l as ProofVariable<L>
                    else (if (eq.r is ProofVariable) eq.r
                    else if (eq.l is Substitutable) eq.l
                    else (eq.r as Substitutable)) as Substitutable<L>
                val s = if (eq.l == v) eq.r else eq.l
                Triple(eq, v, s)
            }
        substs.forEach { (eq, v, s) ->
            val refs = references[v]!!.toSet()  // avoids concurrentmodificationexception
            refs.forEach {
                if (it != eq) {
                    removeReferences(it)
                    it.l = substitute(v, s, it.l)
                    it.r = substitute(v, s, it.r)
                    addReferences(it)
                }
            }
        }
        // Because we make modifications inplace, we need to check that the constraint is even the same as when we began
        val toRemove =
            substs.mapNotNull { (eq, v, s) -> if (v is ProofVariable<*> && ((eq.l == v && eq.r == s) || eq.r == v && eq.l == s)) eq else null }
        constraints.removeAll {
            if (it in toRemove && it is EqualityConstraint<L>) removeReferences(it)
            it in toRemove
        }
        return substs.isNotEmpty()
    }

    private fun splits(): Boolean {
        val newConstrs = mutableListOf<Constraint<L>>()
        fun splittable(c: Constraint<L>) =
            c is EqualityConstraint<L> && c.l is CTypeConstructor<L> && c.r is CTypeConstructor<L>

        /** @returns new constraints from splitting [c], or [c] if it was not split. */
        fun split(c: EqualityConstraint<L>): List<Constraint<L>> {
            if (splittable(c)) {
                val result = (c.l as CTypeConstructor<L>).split(c.r as CTypeConstructor<L>)
                if (result == null) {
                    error = true
                    return listOf(c)
                }
                return result.filter { it !is EqualityConstraint } + result.filterIsInstance<EqualityConstraint<L>>()
                    .flatMap { split(it) }
            }
            return listOf(c)
        }

        for (constr in constraints.filterIsInstance<EqualityConstraint<L>>()) {
            val tmp = split(constr)
            if (error) return false
            newConstrs.addAll(tmp)
        }
        if (error) return false
        val changed = constraints.removeAll {
            val r = splittable(it)
            if (r && it is EqualityConstraint<L>) removeReferences(it)
            r
        }
        newConstrs.filterIsInstance<EqualityConstraint<L>>().forEach { addReferences(it) }
        constraints.addAll(newConstrs)
        return changed
    }
}

/*
Handling conflicts:
- conflict analysis - small set of assignments in DAG that separates conflict from roots (cut)
- two literal watching - only check clauses for which the variable set is one of the two that is being watched
    I think we cannot really do this but maybe it's not so bad bc each constraint has at most two inst() nodes
 */

fun main() {
    val t = ConsTest
    println(t.query.names)
    val ty = Candidate(
        t.query.names, listOf(
            ConcreteL(0, listOf()),
            ConcreteL(1, listOf(ConcreteL(1, listOf(ConcreteL(0, listOf()))))),
            ConcreteL(1, listOf(ConcreteL(0, listOf()))),
            ConcreteL(1, listOf(ConcreteL(2, listOf()))),
            NArrow(
                ConcreteV(0), NArrow(
                    ConcreteL(1, listOf(ConcreteV(0))),
                    ConcreteL(1, listOf(ConcreteHole(false, null, mapOf(0 to 0, 1 to 1, 2 to 0)))),
                    false
                ),
                false
            ),
            ConcreteL(2, listOf())
        )
    )


    val constrs = Unification(ty, t.query.posExsBeforeSubexprs).get()
    println(constrs)
}
