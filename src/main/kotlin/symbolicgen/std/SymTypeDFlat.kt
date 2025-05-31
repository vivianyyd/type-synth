package symbolicgen.std

import symbolicgen.stc.SymTypeC

/** Symbolic types with annotations on variables and labels: F/L with label/VB/VR/VL */
sealed interface SymTypeDFlat
sealed interface NotF : SymTypeDFlat

fun SymTypeC.flatten(): SymTypeDFlat = when (this) {
    is symbolicgen.stc.F -> {
        var curr = this
        val args = mutableListOf<SymTypeC>()
        while (curr is symbolicgen.stc.F) {
            args.add(curr.left)
            curr = curr.rite
        }
        F(args.map { it.flatten() }, curr.flatten() as NotF)
    }
    is symbolicgen.stc.L -> L(this.label)
    is symbolicgen.stc.VB -> VB(this.vId, this.tId)
    is symbolicgen.stc.VL -> VL(this.vId, this.tId)
    is symbolicgen.stc.VR -> VR(this.vId, this.tId)
}

data class F(val args: List<SymTypeDFlat>, val rite: NotF) : SymTypeDFlat {
    override fun toString(): String =
        "${args.joinToString(separator = "->") { if (it is F) "($it)" else "$it" }} -> $rite"
}

class L(val label: Int) : NotF {
    override fun toString(): String = "L$label"
}

sealed class Var(open val vId: Int, open val tId: Int) : NotF {
    override fun toString(): String = "${tId}_$vId"
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
