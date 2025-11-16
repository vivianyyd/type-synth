package core

/** The unification that accepts everything. */
class Empty<L : Language> : Unification<L> {
    override fun holeEquals(hole: Hole<L>): List<CTypeConstructor<L>>? = null

    override fun spawnAndRefine(refinements: List<Pair<Hole<L>, SearchNode<L>>>): Unification<L> = this

    override fun ok(): Boolean = true

    override fun constraints(): List<Constraint<L>>? = listOf()
}
