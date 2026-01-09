package oneast

interface Type {
    fun instantiate(instId: Int): ConstraintTy
}

sealed class BranchType(open val params: List<Type>) : Type

data class Variable(val v: Int) : Type {
    override fun instantiate(instId: Int): ConstraintTy = ConstraintVariable(v, instId)
}

data class Arrow(val l: Type, val r: Type) : BranchType(listOf(l, r)) {
    override fun instantiate(instId: Int): ConstraintTy =
        ConstraintArrow(l.instantiate(instId), r.instantiate(instId))
}

/** Could also be called DefinedLabel? */
data class NamedLabel(val label: Int, override val params: List<Type>) : BranchType(params) {
    override fun instantiate(instId: Int): ConstraintTy =
        ConstraintLabel(label, params.map { it.instantiate(instId) })
}

sealed class THole : Type {
    companion object {
        var nextId = 0

        /** So the numbers are smaller for readability. Only call me between phases */
        fun resetIds() {
            nextId = 0
        }
    }

    val id = nextId++

    override fun instantiate(instId: Int): ConstraintTy = InstantiationTy(this, instId)
}

class TypeHole : THole()

class UnnamedLabel : THole()

interface ConstraintTy

// TODO Consider whether I want two different types of instantiations for TypeHoles vs
//   UnnamedLabels. UnnamedLabels behave differently from TypeHoles because while their
//   instantiated types can differ, they always have the same root. Does it matter?
data class InstantiationTy(val hole: THole, val instId: Int) : ConstraintTy

data class ConstraintVariable(val v: Int, val instId: Int) : ConstraintTy

sealed class TypeConstructor(open val params: List<ConstraintTy>) : ConstraintTy {
    /** Whether this node shallow matches with [other]. */
    abstract fun match(other: TypeConstructor): Boolean

    open fun split(other: TypeConstructor) {
        if (match(other)) params.zip(other.params).map { (a, b) -> TODO() } else null
    }
}

data class ConstraintArrow(val l: ConstraintTy, val r: ConstraintTy) :
    TypeConstructor(listOf(l, r)) {
    override fun match(other: TypeConstructor) = other is ConstraintArrow
}

data class ConstraintLabel(val label: Int, override val params: List<ConstraintTy>) :
    TypeConstructor(params) {
    override fun match(other: TypeConstructor) = other is ConstraintLabel && label == other.label
}
