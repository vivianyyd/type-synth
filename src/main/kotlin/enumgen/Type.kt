package enumgen

sealed interface Type

interface Name
data class NameLiteral(val name: String) : Name
class NameHole : Name {
    override fun toString(): String = "??"
}

data class Variable(val id: NameLiteral) : Type {
    override fun toString(): String =
        "Variable(${id.name})"
}

data class Function(val param: Type, val out: Type) : Type

data class Node(val label: Name, val typeParams: List<Type>) : Type

/** Unifies with everything, producing itself. Represents a type that can never successfully resolve. */
data class Error(val t1: Type, val t2: Type, val category: ErrorCategory) : Type

enum class ErrorCategory {
    NODE_FUNCTION,
    LABEL_MISMATCH,
    PARAM_QUANTITY_MISMATCH,
    APPLIED_NON_FUNCTION,
    VAR_REFERENCES_SELF
}

/**
 * Unifies with everything, producing the other type. Represents a hole/tree not yet completely enumerated.
 *
 * Needs to be a class rather than Object since we want to have pointers to distinct holes
 */
class TypeHole : Type {
    // We want physical equals and for some reason the compiler complains if we don't do this
    override fun equals(other: Any?): Boolean = this === other
    override fun hashCode(): Int = System.identityHashCode(this)
    override fun toString(): String = "??"
}

// TODO how do we use negative examples in pruning? We prune when something fails a positive example and we know where
//  to prune bc of unify algo. But with negative examples, we don't know where the failure was supposed to be, only that
//  we erroneously accept a negative example.