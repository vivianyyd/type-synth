package util

import oneast.*
import query.Example

interface GroundTruth {
    fun valid(example: Example): Boolean
}

/** Computes types of applications based on types of named values, given as [secret] */
class CheckingGroundTruthOracle(secret: Map<String, Type>) : GroundTruth, Oracle {
    // This doesn't enforce the invariant that a label must have the same arity always
    private val truth = stateFromSecret(secret)

    override fun valid(example: Example): Boolean = OneUnification(truth, listOf(example)).ok

    override fun equal(a: Example, b: Example): Boolean {
        val u = OneUnification(truth, listOf(a, b))
        val ta = u.type(a)?.toNode()
        val tb = u.type(b)?.toNode()
        // TODO this should work modulo alpha equivalence
        // Constraint variables are no longer data classes, so we convert them to nodes here which
        // is kind of janky
        return ta != null && tb != null && ta == tb
    }

    override fun dummy(e: Example): Int = OneUnification(truth, listOf(e)).type(e).hashCode()
}

private fun Type.labels(): Set<Pair<Int, Int>> =
    when (this) {
        is Arrow -> l.labels() + r.labels()
        is NamedLabel -> params.flatMap { it.labels() }.toSet() + (label to params.size)
        is THole,
        is Variable -> emptySet()
    }

fun stateFromSecret(secret: Map<String, Type>): SearchState {
    val labelArities = secret.values.flatMap { it.labels() }.toSet().toMap()
    val (names, types) = secret.toList().unzip()
    return SearchState(
        names = names.withIndex().associate { it.value to it.index }, types = types, labelArities
    )
}
