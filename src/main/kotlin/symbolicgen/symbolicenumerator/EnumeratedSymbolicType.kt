package symbolicgen.symbolicenumerator

import util.UnionFind

/** Symbolic types with annotations on variables */
sealed interface EnumeratedSymbolicType

sealed class Var(open val vId: Int, open val tId: Int) : EnumeratedSymbolicType {
    override fun toString(): String = "${tId}_$vId"
}

class L(val label: Int) : EnumeratedSymbolicType {
    override fun toString(): String = "L$label"
}

data class F(val left: EnumeratedSymbolicType, val rite: EnumeratedSymbolicType) : EnumeratedSymbolicType {
    override fun toString(): String = "${if (left is F) "($left)" else "$left"} -> $rite"
}

data class VB(override val vId: Int, override val tId: Int) : Var(vId, tId) {
    override fun toString(): String = "${tId}_$vId"
}

data class VR(override val vId: Int, override val tId: Int) : Var(vId, tId) {
    override fun toString(): String = "${tId}_$vId"
}

data class VL(override val vId: Int, override val tId: Int) : Var(vId, tId) {
    override fun toString(): String = "${tId}_$vId"
}

typealias Binding = Triple<Int, Int, EnumeratedSymbolicType>

fun applyBinding(
    t: EnumeratedSymbolicType,
    varId: Int,
    tId: Int,
    sub: EnumeratedSymbolicType
): EnumeratedSymbolicType =
    when (t) {
        is L, is VB, is VL -> t
        is F -> F(applyBinding(t.left, varId, tId, sub), applyBinding(t.rite, varId, tId, sub))
        is VR -> if (t.vId == varId && t.tId == tId) sub else t
    }

fun applyBindings(t: EnumeratedSymbolicType, bindings: List<Binding>): EnumeratedSymbolicType =
    bindings.fold(t) { acc, (vId, tId, sub) -> applyBinding(acc, vId, tId, sub) }


/*
TODO {f=0_0 -> 0_0, g=1_0 -> 1_0, h=(2_0 -> 2_0) -> 2_0, a=L} with example (h f)
 Under current impl, the second 2_0 gets bound to VB(0_0), although we want it to be a reference.
 Do we need VB/VR separation at all?
 Once we fix this, make sure to copy to the sketch version of unify
 */
/** Returns a list of bindings resulting from unifying [arg] with [param], or null if they are incompatible.
 * @modifies [labelClasses]
 * */
fun unify(param: EnumeratedSymbolicType, arg: EnumeratedSymbolicType, labelClasses: UnionFind): List<Binding>? =
    when (param) {
        is VB -> listOf(Binding(param.vId, param.tId, arg))
        is L -> when (arg) {
            is L -> {
                labelClasses.union(param.label, arg.label)
                listOf()
            }
            is VL -> listOf() // TODO hack
            is F, is VB, is VR -> null
        }
        is F -> when (arg) {
            is L, is VB, is VR -> null
            is VL -> listOf() // TODO hack and might be wrong
            is F -> {
                val leftBindings = unify(param.left, arg.left, labelClasses)
                val riteBindings =
                    leftBindings?.let { applyBindings(param.rite, it) }?.let { unify(it, arg.rite, labelClasses) }
                riteBindings?.let { leftBindings + riteBindings }
            }
        }
        is VL -> listOf()
        is VR -> throw Exception("Invariant broken")
    }

/**
 * Returns the output type of [fn] on input [arg] with no free variables, or null if [arg] is invalid for [fn].
 * @modifies [labelClasses]
 */
fun apply(fn: F, arg: EnumeratedSymbolicType, labelClasses: UnionFind): EnumeratedSymbolicType? {
    if (arg is VR) throw Exception("Invariant broken")
    return unify(fn.left, arg, labelClasses)?.let {
        applyBindings(fn.rite, it)
    }
}
