package core.unification

import core.languages.*
import query.App
import query.Example
import query.Name
import util.Counter

/** Unification that explicitly represents constraints. */
class ConstraintUnification<L : Language> : Unification<L> {
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

    override fun constraints() = get()

    override fun ok() = !error

    override fun holeEquals(hole: Int): List<ConstraintType<L>> =
        constraints.filterIsInstance<EqualityConstraint<L>>().mapNotNull {
            if (it.l is Instantiation && (it.l as Instantiation<L>).n.holeId == hole) it.r
            else if (it.r is Instantiation && (it.r as Instantiation<L>).n.holeId == hole) it.l
            else null
        }

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

    override fun spawnAndRefine(refinements: List<Pair<Hole<L>, SearchNode<L>>>): Unification<L> {
        val new = spawn()
        new.commitAndCheckValid(refinements)
        return new
    }

    private fun spawn() = ConstraintUnification(constraints)

    private fun commitAndCheckValid(refinements: List<Pair<Hole<L>, SearchNode<L>>>): Boolean {
        betterCommit(refinements)
        if (error) refinements.forEach { it.first.conflict() }
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
                if (error) return false
                if (constraints[j] is EqualityConstraint<L>) {
                    val constr = constraints[j] as EqualityConstraint<L>

                    // TODO I am ugly and very bad. This should be a visitor pattern
                    fun newGuy(n: ConstraintType<L>): ConstraintType<L> = when (n) {
                        is Instantiation -> if (n in hole.instantiations()) node.instantiate(
                            n.freshIdGen, n.inst
                        ) else n
                        is CArrow -> CArrow(newGuy(n.l), newGuy(n.r))
                        is ConcreteConstrL -> ConcreteConstrL(
                            n.label,
                            n.params.map { newGuy(it as ConstraintType<L>) as ConstraintType<Concrete> }.toMutableList()
                        ) as ConstraintType<L>
                        is SketchConstrL -> SketchConstrL(
                            n.label,
                            n.params.map { newGuy(it as ConstraintType<L>) as ConstraintType<Sketch> }
                                .toMutableList()
                        ) as ConstraintType<L>
                        is CVariable, InitConstrL, ElabConstrL, is ElaboratedConstrL -> n
                    }

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

        if (error) return
        val c1set = constraints.toSet()
        constraints.clear()
        constraints.addAll(c1set)
        var substChange = substs()
        var splitChange = splits()
        while (splitChange || substChange) {
            if (error) return
            trivial()
            val cset = constraints.toSet()
            constraints.clear()
            constraints.addAll(cset)
            substChange = if (splitChange) substs() else false
            splitChange = if (substChange) splits() else false
        }
        if (error) return
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
                val p = t.params.map { substitute(v, s, it) }
                (when (t) {
                    is CArrow -> CArrow(p)
                    is SketchConstrL -> SketchConstrL(t.label, p as List<ConstraintType<Sketch>>)
                    is ConcreteConstrL -> ConcreteConstrL(t.label, p as List<ConstraintType<Concrete>>)
                    InitConstrL, ElabConstrL, is ElaboratedConstrL -> t
                } as ConstraintType<L>)

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
            if (splittable(constr)) {
                val tmp = split(constr)
                if (error) return false
                newConstrs.addAll(tmp)
            }
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
