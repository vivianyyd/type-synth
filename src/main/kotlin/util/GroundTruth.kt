package util

import oneast.*
import query.Example

interface GroundTruth {
    fun valid(example: Example): Boolean

    /** Whether every one of [examples] is valid. Override when checking them together is cheaper. */
    fun allValid(examples: Collection<Example>): Boolean = examples.all { valid(it) }
}

/** Remembers [truth]'s answers, and only asks it about examples it hasn't answered before. */
class MemoizedGroundTruth(private val truth: GroundTruth) : GroundTruth {
    private val known = HashMap<Example, Boolean>()

    override fun valid(example: Example): Boolean = known.getOrPut(example) { truth.valid(example) }

    override fun allValid(examples: Collection<Example>): Boolean {
        val unknown = examples.filter { known[it] != true }.distinct()
        if (unknown.any { known[it] == false }) return false
        return when (unknown.size) {
            0 -> true
            1 -> valid(unknown.single())
            // A failed batch doesn't say which example failed, so only a passing one is remembered.
            else -> truth.allValid(unknown).also { ok -> if (ok) unknown.forEach { known[it] = true } }
        }
    }
}

/** Computes types of applications based on types of named values, given as [secret] */
class CheckingGroundTruthOracle(secret: Map<String, Type>) : GroundTruth, Oracle {
    // This doesn't enforce the invariant that a label must have the same arity always
    val truth = stateFromContext(secret)

    override fun valid(example: Example): Boolean = OneUnification(truth, listOf(example)).ok

    // type() builds the expression in a graph of its own, so passing the expressions this is about
    // to be asked about would only check them twice.
    override fun equal(a: Example, b: Example): Boolean {
        val u = OneUnification(truth, emptyList())
        val ta = u.type(a)
        val tb = u.type(b)
        return ta != null && tb != null && equalUpToVariableRenaming(ta, tb)
    }

    override fun dummy(e: Example): Int = OneUnification(truth, emptyList()).type(e).hashCode()
}

fun stateFromContext(context: Map<String, Type>): SearchState {
    val labelArities = context.values.flatMap { it.labels() }.toSet().toMap()
    val (names, types) = context.toList().unzip()
    return SearchState(
        names = names.withIndex().associate { it.value to it.index }, types = types, labelArities
    )
}