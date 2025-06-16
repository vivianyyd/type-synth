package types

/**
 * Returns the output type of [fn] on input [arg] with no free variables, or null if [arg] is invalid for [fn].
 * @modifies [labelClasses]
 */
fun applyOrError(fn: Function, arg: Type): OrError<Type> {
    val bindings = unifyOrError(fn.left, arg)
    return if (bindings is Err) Err(bindings.error) else Ok(applyBindings(fn.rite, (bindings as Ok).result))
}

/** Returns a list of bindings resulting from unifying [arg] with [param], or null if they are incompatible.
 * @modifies [labelClasses]
 * */
fun unifyOrError(param: Type, arg: Type): OrError<List<Binding>> =
    when (param) {
        is Error, is TypeHole -> throw Error("Illegal")
        is Function -> when (arg) {
            is Error, is TypeHole -> throw Error("Illegal")
            is Variable -> Err(ErrorCategory.UNBOUND_VARIABLE)
            is LabelNode -> Err(ErrorCategory.PASSED_LABEL_AS_FN)
            is Function -> {
                val leftBindings = unifyOrError(param.left, arg.left)
                val riteBindings = if (leftBindings is Err) leftBindings else
                    unifyOrError(applyBindings(param.rite, (leftBindings as Ok).result), arg.rite)
                riteBindings.bind { Ok((leftBindings as Ok).result + (riteBindings as Ok).result) }
            }
        }
        is LabelNode -> when (arg) {
            is Error, is TypeHole -> throw Error("Illegal")
            is Variable -> Err(ErrorCategory.UNBOUND_VARIABLE)
            is Function -> Err(ErrorCategory.PASSED_FN_AS_LABEL)
            is LabelNode -> {
                if (param.label != arg.label) Err(ErrorCategory.LABEL_MISMATCH)
                else if (param.params.size != arg.params.size) Err(ErrorCategory.PARAM_QUANTITY_MISMATCH)
                else param.params.zip(arg.params)
                    .fold(Ok(listOf())) { acc: OrError<List<Binding>>, (p, a) ->
                        acc.bind { unifyOrError(p, a).bind { Ok((acc as Ok).result + it) } }
                    }
            }
        }
        is Variable -> Ok(listOf(Binding(param.id, arg)))
    }

sealed interface OrError<T> {
    fun bind(f: (T) -> OrError<T>): OrError<T> = when (this) {
        is Err -> this
        is Ok -> f(this.result)
    }
}

data class Ok<T>(val result: T) : OrError<T>
data class Err<T>(val error: ErrorCategory) : OrError<T>
