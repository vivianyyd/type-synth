package core.languages

import core.unification.*
import util.Counter

/** Defines locations of type constructors vs variables and function arities */
object Init : Language

object InitV : Leaf<Init> {
    override fun toString() = "V"

    override fun instantiate(freshIdGen: Counter, instId: Int): ConstraintType<Init> = InitConstrV

    override fun variableNames() = emptySet<Int>()
}

object InitL : Leaf<Init> {
    override fun toString() = "L"

    override fun instantiate(freshIdGen: Counter, instId: Int): ConstraintType<Init> = InitConstrL

    override fun variableNames() = emptySet<Int>()
}

class InitHole : Hole<Init>() {
    /**
     * val so we can prioritize holes correctly, but must be lazy, we only use it when expanding,
     * otherwise stackoverflow lol
     */
    val fnExpansion by lazy { NArrow(InitHole(), InitHole(), true) }

    override fun expansions(
        unification: Unification<Init>,
        vars: Int,
        mustBeLeaf: Boolean
    ): List<SearchNode<Init>> {
        val mustBeCompatible = unification.holeEqualsConstructors(this)
        val fn =
            if (mustBeLeaf) listOf()
            else if (mustBeCompatible.any { it is CArrow }) listOf(fnExpansion) else listOf()
        return listOf(InitV, InitL) + fn
    }

    override fun fastForward(unification: Unification<Init>, vars: Int): SearchNode<Init>? = null
}
