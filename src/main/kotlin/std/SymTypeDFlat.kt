package std

import stc.SymTypeC

/** Symbolic types with annotations on variables and labels: F/L with label/Var */
sealed interface SymTypeDFlat
sealed interface NotF : SymTypeDFlat

fun SymTypeC.flatten(): SymTypeDFlat = when (this) {
    is stc.F -> {
        var curr = this
        val args = mutableListOf<SymTypeC>()
        while (curr is stc.F) {
            args.add(curr.left)
            curr = curr.rite
        }
        F(args.map { it.flatten() }, curr.flatten() as NotF)
    }
    is stc.L -> L(this.label)
    is stc.Var -> Var(this.vId, this.tId)
}

data class F(val args: List<SymTypeDFlat>, val rite: NotF) : SymTypeDFlat {
    override fun toString(): String =
        "${args.joinToString(separator = "->") { if (it is F) "($it)" else "$it" }} -> $rite"
}

data class L(val label: Int) : NotF {
    override fun toString(): String = "L$label"
}

data class Var(val vId: Int, val tId: Int) : NotF {
    constructor(ids: Pair<Int, Int>) : this(ids.second, ids.first)

    override fun toString(): String = "${tId}_$vId"

    companion object {
        fun toIds(s: String) = s.substringBefore('_').toInt() to s.substringAfter('_').toInt()
    }
}
