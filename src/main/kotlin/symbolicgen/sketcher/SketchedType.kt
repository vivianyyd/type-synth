package symbolicgen.sketcher

sealed interface SketchedType {
    fun constructSketch(): String
}

// TODO Rly horrible code style
data class N(val name: String) : SketchedType {
    override fun constructSketch(): String = throw UnsupportedOperationException("Bad code style, fixme later")
}

object L : SketchedType {
    override fun toString(): String = "L"
    override fun constructSketch(): String = "new Label()"
}

data class F(val left: SketchedType, val rite: SketchedType) : SketchedType {
    override fun toString(): String = "${if (left is F) "($left)" else "$left"} -> $rite"
    override fun constructSketch(): String =
        "new Function(left=${left.constructSketch()}, rite=${rite.constructSketch()})"
}

data class VB(val vId: Int, val tId: Int) : SketchedType {
//    override fun toString(): String = "V"

    override fun toString(): String = "${tId}_$vId"
    override fun constructSketch(): String = "new VarBind(vId=$vId, tId=$tId)"
}

data class VR(val vId: Int, val tId: Int) : SketchedType {
//    override fun toString(): String = "V"

    override fun toString(): String = "${tId}_$vId"
    override fun constructSketch(): String = "new VarRef(vId=$vId, tId=$tId)"
}

object VL : SketchedType {
//    override fun toString(): String = "V"

    override fun toString(): String = "VL"
    override fun constructSketch(): String = "new VarLabelBound()"
}

data class CL(val dummy: Int) : SketchedType {
    override fun toString(): String = "CL"
    override fun constructSketch(): String = "new ConcreteLabel(dummy=$dummy)"
}

typealias Binding = Triple<Int, Int, SketchedType>

fun applyBinding(t: SketchedType, varId: Int, tId: Int, sub: SketchedType): SketchedType = when (t) {
    is CL, L, is VB, VL, is N -> t
    is F -> F(applyBinding(t.left, varId, tId, sub), applyBinding(t.rite, varId, tId, sub))
    is VR -> if (t.vId == varId && t.tId == tId) sub else t
}

fun applyBindings(t: SketchedType, bindings: List<Binding>): SketchedType =
    bindings.fold(t) { acc, (vId, tId, sub) -> applyBinding(acc, vId, tId, sub) }

/** Returns a list of bindings resulting from unifying [arg] with [param], or null if they are incompatible. */
fun unify(param: SketchedType, arg: SketchedType): List<Binding>? = when (param) {
    is VB -> listOf(Binding(param.vId, param.tId, arg))
    is CL -> when (arg) {
        is CL -> if (param.dummy == arg.dummy) listOf() else null
        is F -> null
        L, VL -> listOf()
        is VB, is VR, is N -> throw Exception("Invariant broken")
    }
    L -> when (arg) {
        is CL, L -> listOf()
        is F, VL -> null
        is VB, is VR, is N -> throw Exception("Invariant broken")
    }
    is F -> when (arg) {
        is CL, L -> null
        VL -> listOf()
        is F -> {
            val leftBindings = unify(param.left, arg.left)
            val riteBindings = leftBindings?.let { applyBindings(param.rite, it) }?.let { unify(it, arg.rite) }
            riteBindings?.let { leftBindings + riteBindings }
        }
        is VB, is VR, is N -> throw Exception("Invariant broken")
    }
    VL -> listOf()
    is VR, is N -> throw Exception("Invariant broken")
}

/**
Returns the output type of [fn] on input [arg] with no free variables, or null if [arg] is invalid for [fn].
 */
fun apply(fn: F, arg: SketchedType): SketchedType? {
    if (arg is VB || arg is VR) throw Exception("Invariant broken")
    return unify(fn.left, arg)?.let { applyBindings(fn.rite, it) }
}
