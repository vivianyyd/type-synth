package util

import query.*

interface Oracle {
    fun equal(a: Example, b: Example): Boolean

    fun flatEqual(a: FlatApp, b: FlatApp): Boolean = equal(a.unflatten(), b.unflatten())

    fun dummy(e: Example): Int
}

/**
 * Requires [secret[app]] is null iff [app] is a negative example Requires a mapping of *all*
 * positive applications (including all subexpressions) to their dummy types
 */
class ScrappyNewOracle(private val secret: Map<Example, String?>) : Oracle {
    private var fresh = 0
    private val dummies = secret.values.filterNotNull().toSet().associateWith { fresh++ }

    override fun equal(a: Example, b: Example): Boolean =
        if (secret[a] == null || secret[b] == null) false else secret[a] == secret[b]

    override fun dummy(e: Example): Int =
        secret[e]?.let { dummies[it] } ?: throw Exception("Failed oracle precondition")
}

interface EqualityOracle {
    fun equal(a: FlatApp, b: FlatApp): Boolean
}
