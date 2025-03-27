package symbolicgen.sketcher

sealed interface SketchedType {
    fun constructSketch(): String
}

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
    override fun toString(): String = "${tId}_$vId"
    override fun constructSketch(): String = "new VarBind(vId=$vId, tId=$tId)"
}

data class VR(val vId: Int, val tId: Int) : SketchedType {
    override fun toString(): String = "${tId}_$vId"
    override fun constructSketch(): String = "new VarRef(vId=$vId, tId=$tId)"
}

object VL : SketchedType {
    override fun toString(): String = "VL"
    override fun constructSketch(): String = "new VarLabelBound()"
}

data class CL(val dummy: Int) : SketchedType {
    override fun toString(): String = "CL"
    override fun constructSketch(): String = "new ConcreteLabel(dummy=$dummy)"
}
