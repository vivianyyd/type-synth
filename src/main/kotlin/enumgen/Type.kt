package enumgen

sealed interface Type {
    fun recursiveNumChildHoles(): Int
    fun directChildHoles(): Boolean
    /** Number of nodes in the longest path root to leaf */
    val height: Int
}

sealed class AbstractType : Type {
    abstract val children: List<Type>

    override val height: Int by lazy {
        1 + (children.maxOfOrNull { it.height } ?: 0)
    }
}

data class Variable(val id: String) : AbstractType() {
    override fun toString(): String = "v($id)"
    override fun recursiveNumChildHoles() = 0
    override fun directChildHoles() = false
    override val children = listOf<Type>()
}

data class Function(val left: Type, val rite: Type) : AbstractType() {
    override fun toString(): String = "($left) -> $rite"
    override fun recursiveNumChildHoles() = left.recursiveNumChildHoles() + rite.recursiveNumChildHoles()
    override fun directChildHoles() = left is ChildHole || rite is ChildHole
    override val children = listOf(left, rite)
}

data class LabelNode(val label: String, val params: List<Type>) : AbstractType() {
    override fun toString(): String = "{$label of $params}"
    override fun recursiveNumChildHoles() = params.fold(0) { acc, type -> acc + type.recursiveNumChildHoles() }
    override fun directChildHoles() = params.any { it is ChildHole }
    override val children = params
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
    override val children = listOf<Type>()
}

/** A hole to be filled by a child node. */
class ChildHole : TypeHole() {
    override fun toString(): String = "_"
    override fun recursiveNumChildHoles() = 1
    override fun directChildHoles() = false
}

/** A hole to be filled by a sibling node. */
class SiblingHole(val depth: Int) : TypeHole() {
    override fun toString(): String = ".${depth}"
    override fun recursiveNumChildHoles() = 0
    override fun directChildHoles() = false
}

/** Unifies with everything, producing itself. Represents a type that can never successfully resolve. */
data class Error(val t1: Type, val t2: Type, val category: ErrorCategory) : AbstractType() {
    override fun recursiveNumChildHoles() = 0
    override fun directChildHoles() = false
    override val children = listOf<Type>()
}

enum class ErrorCategory {
    NODE_FUNCTION,
    LABEL_MISMATCH,
    PARAM_QUANTITY_MISMATCH,
    APPLIED_NON_FUNCTION,
    VAR_REFERENCES_SELF
}
