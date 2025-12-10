package core.unification

import core.languages.Sketch

data class SketchConstrV(val v: Int, val instId: Int) : Substitutable<Sketch>() {
    override fun toString() = "V${v}-$instId"
}

data class SketchConstrL(val label: Int, override val params: List<ConstraintType<Sketch>>) :
    CTypeConstructor<Sketch>(params) {
    companion object {
        fun new(label: Int, params: List<ConstraintType<Sketch>>) = SketchConstrL(label, params.toMutableList())
    }

    override fun match(other: CTypeConstructor<Sketch>): Boolean =
        other is SketchConstrL && label == other.label

    override fun toString() = "L$label$params"
}
