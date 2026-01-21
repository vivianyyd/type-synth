package benchmarking

import oneast.Arrow
import oneast.NamedLabel
import oneast.Type
import oneast.Variable
import types.Function
import types.LabelNode
import types.Type as LegacyType
import types.Variable as LegacyVariable

fun parseHaskellTypesLegacy(signatures: List<String>): List<Pair<LegacyType, String>> {
    val context = ParseContext()
    return signatures.map { signature ->
        val (type, name) = parseTypeSignature(signature, context)
        type.toLegacyType(context) to name
    }
}

private fun Type.toLegacyType(context: ParseContext): LegacyType =
    when (this) {
        is Variable ->
            LegacyVariable(
                requireNotNull(context.variableNames[this.v]) { "Missing variable ${this.v}" }
            )
        is Arrow -> Function(this.l.toLegacyType(context), this.r.toLegacyType(context))
        is NamedLabel -> {
            val name = requireNotNull(context.labelNames[this.label]) { "Missing label ${this.label}" }
            LabelNode(name, this.params.map { it.toLegacyType(context) })
        }
        else -> error("Unsupported oneast type in legacy conversion")
    }
