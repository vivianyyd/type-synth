package util

import enumgen.types.Type
import enumgen.types.checkApplication

interface EqualityNewOracle {
    fun equal(a: Example, b: Example): Boolean
    fun dummy(e: Example): Int
}

/**
 * Requires [secret[app]] is null iff [app] is a negative example
 * Requires a mapping of *all* applications (including all subexpressions) to their dummy types
 */
class ScrappyNewOracle(private val secret: Map<Example, String?>) : EqualityNewOracle {
    private var fresh = 0
    private val dummies = secret.values.filterNotNull().toSet().associateWith { fresh++ }

    override fun equal(a: Example, b: Example): Boolean =
        if (secret[a] == null || secret[b] == null) false else secret[a] == secret[b]

    override fun dummy(e: Example): Int =
        secret[e]?.let { dummies[it] } ?: throw Exception("Failed oracle precondition")
}

interface EqualityOracle {
    fun equal(a: Application, b: Application): Boolean
}

/**
 * Computes types of applications based on types of named values, given as [secret]
 */
class CheckingOracle(private val secret: Map<String, Type>) : EqualityOracle {
    override fun equal(a: Application, b: Application): Boolean =
        checkApplication(a, secret) == checkApplication(b, secret)
}

/**
 * Requires [secretTypes[app]] is null iff [app] is a negative example
 * Requires a mapping of *all* applications (including all subexpressions) to their dummy types
 */
class ScrappyOracle(private val secret: Map<Application, String?>) : EqualityOracle {
    override fun equal(a: Application, b: Application): Boolean =
        if (secret[a] == null || secret[b] == null) false else secret[a] == secret[b]
}

class PairwiseCheckOracle() : EqualityOracle {
    override fun equal(a: Application, b: Application): Boolean = TODO("memoize results")
}
