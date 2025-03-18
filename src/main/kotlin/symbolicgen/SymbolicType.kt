package symbolicgen

sealed interface SymbolicType

sealed class AbstractType : SymbolicType

object Variable : AbstractType() {
    override fun toString(): String = "V"
}

class Function(val left: SymbolicType, val rite: SymbolicType) : AbstractType() {
    override fun toString(): String = "${if (left is Function) "($left)" else "$left"} -> $rite"
}

object Label: AbstractType() {
    override fun toString(): String = "L"
}

/**
 * Unifies with everything, producing the other type. Represents a hole/tree not yet completely enumerated.
 *
 * Needs to be a class rather than Object since we want to have pointers to distinct holes
 */
sealed class TypeHole : AbstractType() {
    // We want physical equals and for some reason the compiler complains if we don't do this
    override fun equals(other: Any?): Boolean = this === other
    override fun hashCode(): Int = System.identityHashCode(this)
    override fun toString(): String = "??"
}

/** A hole to be filled by a child node. */
class ChildHole : TypeHole() {
    override fun toString(): String = "_"
}

/** A hole to be filled by a sibling node. */
class SiblingHole(val depth: Int) : TypeHole() {
    override fun toString(): String = ".${depth}"
}

/** Unifies with everything, producing itself. Represents a type that can never successfully resolve. */
data class Error(val category: ErrorCategory, val t1: SymbolicType, val t2: SymbolicType? = null) : AbstractType()

enum class ErrorCategory {
    LABEL_FUNCTION,
    APPLIED_NON_FUNCTION
}
