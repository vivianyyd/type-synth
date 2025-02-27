package enumgen.types

/**
 * TODO Ideally, there should be two type files: One for the notion of type which is shared across all synthesis
 *  implementations, and one which only refines the TypeHoles into Child and Siblings for enumgen.
 *  Then we would inherit from the general notion of type, and add [recursiveNumChildHoles] and [directChildHoles].
 */

fun Type.numParams(): Int = when (this) {
    is LabelNode, is Variable -> 0
    is Function -> 1 + this.rite.numParams()
    is Error, is TypeHole -> throw Exception("What is this")
}

fun Type.recursiveNumChildHoles(): Int = when (this) {
    is ChildHole -> 1
    is Function -> left.recursiveNumChildHoles() + rite.recursiveNumChildHoles()
    is LabelNode -> params.fold(0) { acc, type -> acc + type.recursiveNumChildHoles() }
    is SiblingHole, is Variable, is Error -> 0
}

fun Type.recursiveNumVars(): Int = when (this) {
    is Variable -> 1
    is Function -> left.recursiveNumVars() + rite.recursiveNumVars()
    is LabelNode -> params.fold(0) { acc, type -> acc + type.recursiveNumVars() }
    is TypeHole, is Error -> 0
}

fun Type.directChildHoles(): Boolean = when (this) {
    is Function -> left is ChildHole || rite is ChildHole
    is LabelNode -> params.any { it is ChildHole }
    is TypeHole, is Variable, is Error -> false
}

sealed interface Type {
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
    override fun toString(): String = id
    override val children = listOf<Type>()
}

data class Function(val left: Type, val rite: Type) : AbstractType() {
    override fun toString(): String = "${if (left is Function) "($left)" else "$left"} -> $rite"
    override val children = listOf(left, rite)
}

data class LabelNode(val label: String, val params: List<Type>) : AbstractType() {
    override fun toString(): String = "$label$params"
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
}

/** A hole to be filled by a sibling node. */
class SiblingHole(val depth: Int) : TypeHole() {
    override fun toString(): String = ".${depth}"
}

/** Unifies with everything, producing itself. Represents a type that can never successfully resolve. */
data class Error(val t1: Type, val t2: Type, val category: ErrorCategory) : AbstractType() {
    override val children = listOf<Type>()
}

enum class ErrorCategory {
    NODE_FUNCTION,
    LABEL_MISMATCH,
    PARAM_QUANTITY_MISMATCH,
    APPLIED_NON_FUNCTION,
    VAR_REFERENCES_SELF
}
