package symbolicgen.symbolicsketcher

/** Symbolic types with annotations on variables */
sealed interface SpecializedSymbolicType {
    fun constructSketch(): String
}

sealed class Var(open val vId: Int, open val tId: Int) : SpecializedSymbolicType

// TODO Rly horrible code style
data class N(val name: String) : SpecializedSymbolicType {
    override fun constructSketch(): String = throw UnsupportedOperationException("Bad code style, fixme later")
}

object L : SpecializedSymbolicType {
    override fun toString(): String = "L"
    override fun constructSketch(): String = "new Label()"
}

data class F(val left: SpecializedSymbolicType, val rite: SpecializedSymbolicType) : SpecializedSymbolicType {
    override fun toString(): String = "${if (left is F) "($left)" else "$left"} -> $rite"
    override fun constructSketch(): String =
        "new Function(left=${left.constructSketch()}, rite=${rite.constructSketch()})"
}

data class VB(override val vId: Int, override val tId: Int) : Var(vId, tId) {
//    override fun toString(): String = "V"

    override fun toString(): String = "${tId}_$vId"
    override fun constructSketch(): String = "new VarBind(vId=$vId, tId=$tId)"
}

data class VR(override val vId: Int, override val tId: Int) : Var(vId, tId) {
//    override fun toString(): String = "V"

    override fun toString(): String = "${tId}_$vId"
    override fun constructSketch(): String = "new VarRef(vId=$vId, tId=$tId)"
}

data class VL(override val vId: Int, override val tId: Int) : Var(vId, tId) {
//    override fun toString(): String = "V"

    override fun toString(): String = "${tId}_$vId"
    override fun constructSketch(): String = "new VarLabelBound(vId=$vId, tId=$tId)"
}

data class CL(val dummy: Int) : SpecializedSymbolicType {
    override fun toString(): String = "CL"
    override fun constructSketch(): String = "new ConcreteLabel(dummy=$dummy)"
}

typealias Binding = Triple<Int, Int, SpecializedSymbolicType>

fun applyBinding(
    t: SpecializedSymbolicType,
    varId: Int,
    tId: Int,
    sub: SpecializedSymbolicType
): SpecializedSymbolicType =
    when (t) {
        is CL, L, is VB, is VL, is N -> t
        is F -> F(applyBinding(t.left, varId, tId, sub), applyBinding(t.rite, varId, tId, sub))
        is VR -> if (t.vId == varId && t.tId == tId) sub else t
    }

fun applyBindings(t: SpecializedSymbolicType, bindings: List<Binding>): SpecializedSymbolicType =
    bindings.fold(t) { acc, (vId, tId, sub) -> applyBinding(acc, vId, tId, sub) }


/*
TODO {f=0_0 -> 0_0, g=1_0 -> 1_0, h=(2_0 -> 2_0) -> 2_0, a=L} with example (h f)
 Under current impl, the second 2_0 gets bound to VB(0_0), although we want it to be a reference.
 Do we need VB/VR separation at all?
 Once we fix this, make sure to copy to the sketch version of unify
 */
/** Returns a list of bindings resulting from unifying [arg] with [param], or null if they are incompatible. */
fun unify(param: SpecializedSymbolicType, arg: SpecializedSymbolicType): List<Binding>? = when (param) {
    is VB -> listOf(Binding(param.vId, param.tId, arg))
    is CL -> when (arg) {
        is CL -> if (param.dummy == arg.dummy) listOf() else null
        is F -> null
        L, is VL -> listOf()  // TODO I think we shouldn't see VLs here ever
        is VB, is VR, is N -> throw Exception("Invariant broken")
    }
    L -> when (arg) {
        is CL, L, is VL, is VB, is VR -> listOf() // TODO hack
        is F -> null
        is N -> throw Exception("Invariant broken")
    }
    is F -> when (arg) {
        is CL, L -> null
        is VL, is VB, is VR -> listOf() // TODO hack and might be wrong
        is F -> {
            val leftBindings = unify(param.left, arg.left)
            val riteBindings = leftBindings?.let { applyBindings(param.rite, it) }?.let { unify(it, arg.rite) }
            riteBindings?.let { leftBindings + riteBindings }
        }
        is N -> throw Exception("Invariant broken")
    }
    is VL, is VR, is N -> throw Exception("Invariant broken")
}

/**
Returns the output type of [fn] on input [arg] with no free variables, or null if [arg] is invalid for [fn].
 */
fun apply(fn: F, arg: SpecializedSymbolicType): SpecializedSymbolicType? {
    if (arg is VR) throw Exception("Invariant broken")
    return unify(fn.left, arg)?.let { applyBindings(fn.rite, it) }
}
