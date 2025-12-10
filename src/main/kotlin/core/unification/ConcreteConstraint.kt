package core.unification

import core.languages.Concrete

data class ConcreteConstrV(val v: Int, val instId: Int) : Substitutable<Concrete>() {
    override fun toString() = "V${v}-$instId"
}

data class ConcreteConstrL(val label: Int, override val params: List<ConstraintType<Concrete>>) :
    CTypeConstructor<Concrete>(params) {
    companion object {
        fun new(label: Int, params: List<ConstraintType<Concrete>>) = ConcreteConstrL(label, params.toMutableList())
    }

    override fun match(other: CTypeConstructor<Concrete>): Boolean = other is ConcreteConstrL && label == other.label
    override fun toString() = "L$label$params"
}
