package enumgen

sealed interface Type

data class Variable(val id: String): Type

data class Function(/* TODO val id: String,*/ val param: Type, val out: Type): Type

data class Node(val label: String, val typeParams: List<Type>): Type

object Error: Type

// TODO how do we use negative examples in pruning? We prune when something fails a positive example and we know where
//  to prune bc of unify algo. But with negative examples, we don't know where the failure was supposed to be, only that
//  we erroneously accept a negative example.