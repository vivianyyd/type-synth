package util

import oneast.OneUnification
import oneast.SearchState
import products.types.Type
import products.types.checkApplication
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

/** Computes types of applications based on types of named values, given as [secret] */
class CheckingOracle(private val secret: Map<String, Type>) : Oracle {
    // flatEqual(a.flatten(), b.flatten()) works too. Idk why I did this
    override fun equal(a: Example, b: Example): Boolean {
        val ta = products.check(a, secret)
        val tb = products.check(b, secret)
        return ta != null && tb != null && ta == tb
    }

    override fun flatEqual(a: FlatApp, b: FlatApp): Boolean {
        val ta = checkApplication(a, secret)
        val tb = checkApplication(b, secret)
        return ta !is Error && tb !is Error && ta == tb
    }

    override fun dummy(e: Example): Int = checkApplication(e.flatten(), secret).hashCode()

    fun printSecret() = println(secret.entries.joinToString(separator = "\n"))
}

/** Computes types of applications based on types of named values, given as [secret] */
class NewCheckingOracle(secret: Map<String, oneast.Type>) : Oracle {
    private val names = secret.keys.toList()
    private val nameMap = names.withIndex().associate { (i, name) -> name to i }
    private val secret =
        SearchState(
            names = nameMap,
            types = names.map { name -> secret[name]!! },
            // The remaining fields don't matter in an oracle
            rounds = listOf(),
            labelArities = mapOf()
        )

    override fun equal(a: Example, b: Example): Boolean {
        val u = OneUnification(secret, listOf(a, b))
        val ta = u.type(a)
        val tb = u.type(b)
        return ta != null && tb != null && ta == tb
    }

    override fun flatEqual(a: FlatApp, b: FlatApp) = equal(a.unflatten(), b.unflatten())

    override fun dummy(e: Example): Int = OneUnification(secret, listOf(e)).type(e).hashCode()
}

/**
 * Requires [secretTypes[app]] is null iff [app] is a negative example Requires a mapping of *all*
 * applications (including all subexpressions) to their dummy types
 */
class ScrappyOracle(private val secret: Map<FlatApp, String?>) : EqualityOracle {
    override fun equal(a: FlatApp, b: FlatApp): Boolean =
        if (secret[a] == null || secret[b] == null) false else secret[a] == secret[b]
}

class PairwiseCheckOracle : EqualityOracle {
    override fun equal(a: FlatApp, b: FlatApp): Boolean = TODO("memoize results")
}
