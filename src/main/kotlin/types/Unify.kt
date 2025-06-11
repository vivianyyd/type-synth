package types

typealias Binding = Pair<String, Type>

fun applyBinding(
    t: Type,
    v: String,
    sub: Type
): Type =
    when (t) {
        is Error, is TypeHole -> throw Error("Illegal")
        is Function -> Function(applyBinding(t.left, v, sub), applyBinding(t.rite, v, sub))
        is LabelNode -> LabelNode(t.label, t.params.map { applyBinding(it, v, sub) })
        is Variable -> if (t.id == v) sub else t
    }

fun applyBindings(t: Type, bindings: List<Binding>): Type =
    bindings.fold(t) { acc, (v, sub) -> applyBinding(acc, v, sub) }

/** Returns a list of bindings resulting from unifying [arg] with [param], or null if they are incompatible.
 * @modifies [labelClasses]
 * */
fun unify(param: Type, arg: Type): List<Binding>? =
    when (param) {
        is Error, is TypeHole -> throw Error("Illegal")
        is Function -> when (arg) {
            is Error, is TypeHole -> throw Error("Illegal")
            is LabelNode, is Variable -> null
            is Function -> {
                val leftBindings = unify(param.left, arg.left)
                val riteBindings =
                    leftBindings?.let { applyBindings(param.rite, it) }?.let { unify(it, arg.rite) }
                riteBindings?.let { leftBindings + riteBindings }
            }
        }
        is LabelNode -> when (arg) {
            is Error, is TypeHole -> throw Error("Illegal")
            is Function, is Variable -> null
            is LabelNode -> if (param.label == arg.label) param.params.zip(arg.params)
                .fold(listOf()) { acc: List<Binding>?, (p, a) ->
                    acc?.let { unify(p, a)?.let { acc + it } }
                }
            else null
        }
        is Variable -> listOf(Binding(param.id, arg))
    }

/**
 * Returns the output type of [fn] on input [arg] with no free variables, or null if [arg] is invalid for [fn].
 * @modifies [labelClasses]
 */
fun apply(fn: Function, arg: Type): Type? = unify(fn.left, arg)?.let {
    applyBindings(fn.rite, it)
}
