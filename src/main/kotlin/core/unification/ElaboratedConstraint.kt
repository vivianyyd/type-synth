package core.unification

import core.languages.Elaborated

data class ElaboratedConstrV(val v: Int, val instId: Int) : Substitutable<Elaborated>() {
    override fun toString() = "V${v}-$instId"
}

data class ElaboratedConstrL(val label: Int) : CTypeConstructor<Elaborated>(mutableListOf()) {
    override fun match(other: CTypeConstructor<Elaborated>): Boolean = other is ElaboratedConstrL

    override fun toString() = "L$label"

    override fun split(other: CTypeConstructor<Elaborated>): List<Constraint<Elaborated>>? {
        return super.split(other)?.plus(LabelConstraint(label, (other as ElaboratedConstrL).label))
    }
}

data class LabelConstraint(val a: Int, val b: Int) : Constraint<Elaborated> {
    override fun toString() = "L$a == L$b"

    override fun trivial() = a == b

    override fun copy() = this
}
