package core.languages

import core.unification.ConstraintType
import core.unification.ElabConstrL
import core.unification.ElabConstrV
import core.unification.Unification
import util.Counter

object Elab : Language

data class ElabV(val v: Int) : Leaf<Elab> {
    override fun toString() = "V$v"

    override fun instantiate(freshIdGen: Counter, instId: Int): ConstraintType<Elab> =
        ElabConstrV(v, instId)

    override fun variableNames() = setOf(v)
}

object ElabL : Leaf<Elab> {
    override fun toString() = "L"

    override fun instantiate(freshIdGen: Counter, instId: Int): ConstraintType<Elab> = ElabConstrL

    override fun variableNames() = emptySet<Int>()
}

class ElabVarHole : Hole<Elab>() {
    override fun toString() = "V_${holeId}_"

    override fun expansions(
        unification: Unification<Elab>,
        vars: Int,
        mustBeLeaf: Boolean
    ): List<SearchNode<Elab>> = (0 until vars + 1).map { ElabV(it) }

    override fun fastForward(unification: Unification<Elab>, vars: Int): SearchNode<Elab>? = null

    // TODO Not sure if this does what I want to do.
    //    override fun equals(other: Any?) = other is ElabVarHole
    //    override fun hashCode() = 0
}
