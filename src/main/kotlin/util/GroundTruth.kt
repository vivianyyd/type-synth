package util

import oneast.*
import query.Example

interface GroundTruth {
    fun valid(example: Example): Boolean
}

/** Computes types of applications based on types of named values, given as [secret] */
class CheckingGroundTruthOracle(secret: Map<String, Type>) : GroundTruth, Oracle {
    // This doesn't enforce the invariant that a label must have the same arity always
    private val truth = stateFromContext(secret)

    override fun valid(example: Example): Boolean = OneUnification(truth, listOf(example)).ok

    // type() builds the expression in a graph of its own, so passing the expressions this is about
    // to be asked about would only check them twice.
    override fun equal(a: Example, b: Example): Boolean {
        val u = OneUnification(truth, emptyList())
        val ta = u.type(a)
        val tb = u.type(b)
        return ta != null && tb != null && equalInEmptyLabelContext(ta, tb)
    }

    override fun dummy(e: Example): Int = OneUnification(truth, emptyList()).type(e).hashCode()
}

private fun Type.labels(): Set<Pair<Int, Int>> =
    when (this) {
        is Arrow -> l.labels() + r.labels()
        is NamedLabel -> params.flatMap { it.labels() }.toSet() + (label to params.size)
        is THole,
        is Variable -> emptySet()
    }

fun stateFromContext(context: Map<String, Type>): SearchState {
    val labelArities = context.values.flatMap { it.labels() }.toSet().toMap()
    val (names, types) = context.toList().unzip()
    return SearchState(
        names = names.withIndex().associate { it.value to it.index }, types = types, labelArities
    )
}