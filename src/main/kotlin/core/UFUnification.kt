package core

import query.App
import query.Example
import query.Name
import util.Counter
import util.UnionFind

/** Unification that explicitly represents constraints as a union-find data structure. */
class UFUnification<L : Language> private constructor(
    private val uf: UnionFind<ConstraintType<L>> = UnionFind { it is CTypeConstructor<L> },
    private val instVarId: Counter = Counter(),
    private val proofVarId: Counter = Counter(),
    private var error: Boolean = false,
    private val insts: Counter = Counter(),  // Number of times any top-level type has been instantiated
    private val customConstraints: MutableList<Constraint<L>> = mutableListOf()
) : Unification<L> {
    constructor(candidate: Candidate<L>, exs: List<Example>) : this() {
        fun constrainType(ex: Example): ConstraintType<L> = when (ex) {
            is Name -> candidate.searchNodeOf(ex.name).instantiate(instVarId, insts.get())
            is App -> {
                val proofVariable = ProofVariable<L>(proofVarId.get())
                val a = constrainType(ex.fn)
                val b = CArrow(constrainType(ex.arg), proofVariable)
                unify(a, b)
                proofVariable
            }
        }
        exs.forEach { constrainType(it) }
        substs()
    }

    private fun unify(a: ConstraintType<L>, b: ConstraintType<L>) {
        val ta = uf.find(a)
        val tb = uf.find(b)
        if (ta is CTypeConstructor<L> && tb is CTypeConstructor<L>) {
            val (equalities, custom) = ta.split(tb)?.partition { it is EqualityConstraint } ?: run {
                error = true
                return
            }
            (equalities as List<EqualityConstraint<L>>).forEach { unify(it.l, it.r) }
            customConstraints.addAll(custom)
        } else if (ta is CVariable<L> || tb is CVariable<L>) {
            uf.union(ta, tb)
//            addReferences(ta)
//            addReferences(tb)
        } else throw Error("Cannot unify $a and $b: Something wrong with subtype casing")
    }

    override fun holeEquals(hole: Int): List<ConstraintType<L>> =
        uf.rootsFor { it is Instantiation && it.n.holeId == hole }

    override fun spawnAndRefine(refinements: List<Pair<Hole<L>, SearchNode<L>>>): Unification<L> {
        val new = spawn()
        new.commitAndCheckValid(refinements)
        return new
    }

    private fun spawn() =
        UFUnification(
            uf.copy(),
            instVarId.copy(),
            proofVarId.copy(),
            error,
            insts.copy(),
            customConstraints.map { it.copy() }.toMutableList()
        )

    private fun commitAndCheckValid(refinements: List<Pair<Hole<L>, SearchNode<L>>>): Boolean {
        refinements.forEach { (hole, node) ->
            // for each instantiation variable for this node,
            uf.filterNodes { it is Instantiation && it in hole.instantiations() }
                .filterIsInstance<Instantiation<L>>(/*redundant but for cast*/).forEach {
                    // instantiate node with the correct ids and
                    // unify the instantiated replacement type with the canonical node of the inst
                    unify(uf.find(it), node.instantiate(it.freshIdGen, it.inst))
                    if (error) return false
                }
        }
        substs()
        return true
        // TODO we can remove proof variables from the eqclasses once they are resolved
    }

    override fun ok(): Boolean = !error

    /** Careful, I only return the custom ones! */
    override fun constraints(): List<Constraint<L>>? = if (error) null else customConstraints

    private fun substs() {
        // TODO make me less awful
        fun transform(t: ConstraintType<L>): ConstraintType<L> = when (t) {
            is CTypeConstructor -> {
                val p = t.params.map { transform(it) }
                (when (t) {
                    is CArrow -> CArrow(p)
                    is ConcreteConstrL -> ConcreteConstrL(t.label, p as List<ConstraintType<Concrete>>)
                    is SketchConstrL -> SketchConstrL(t.label, p as List<ConstraintType<Sketch>>)
                    InitConstrL, ElabConstrL, is ElaboratedConstrL -> t
                } as ConstraintType<L>)
            }
            is Substitutable, is Instantiation -> uf.find(t)
            is InitConstrV -> t
        }
        // TODO I can use references to micro-opt
        val transformedRoots = uf.allRootValues().associateWith { transform(it) }
        // For each root, perform as many substs from variables to other roots as possible
        uf.replaceRoots(transformedRoots)
    }
}
