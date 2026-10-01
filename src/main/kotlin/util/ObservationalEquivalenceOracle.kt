package util

import query.*

/**
 * Decides whether two expressions have the same type without knowing any types, using only
 * [examples] and a [truth] that says whether an expression is well-typed.
 *
 * Two well-typed expressions a and b are equal if swapping them inside the examples never changes
 * what those examples say. For every example containing a, and every nonempty set of occurrences of
 * a in it, those occurrences are replaced by b (and vice versa). A positive example must stay
 * valid. A negative example must stay a *minimal* negative example: invalid, with every strict
 * subexpression valid. The original negative examples are minimal, so if the swap made some strict
 * subexpression invalid, the swapped-in expression fails earlier than the original did.
 *
 * Expressions that don't occur in any example are only checked for validity, so they are equal to
 * anything else that is valid and doesn't occur either.
 *
 * @requires [examples] contains only minimal negative examples.
 */
class ObservationalEquivalenceOracle(
    private val examples: Examples,
    private val truth: GroundTruth,
) : Oracle {
    private val validCache = HashMap<Example, Boolean>()
    private val equalCache = HashMap<Pair<Example, Example>, Boolean>()

    // One representative of each equivalence class dummy() has seen, indexed by the class's dummy
    private val representatives = mutableListOf<Example>()

    private fun valid(e: Example): Boolean = validCache.getOrPut(e) { truth.valid(e) }

    /** Invalid, but every strict subexpression is valid. A name is always valid. */
    private fun minimalNegative(e: Example): Boolean =
        when (e) {
            is Name -> false
            // A subexpression of a valid expression is valid, so checking the children is enough.
            is App -> !valid(e) && valid(e.fn) && valid(e.arg)
        }

    override fun equal(a: Example, b: Example): Boolean {
        if (!valid(a) || !valid(b)) return false
        if (a == b) return true
        val key = if (a.hashCode() <= b.hashCode()) a to b else b to a
        return equalCache.getOrPut(key) { substitutable(a, b) && substitutable(b, a) }
    }

    /** Replacing occurrences of [from] with [to] never changes the outcome of any example. */
    private fun substitutable(from: Example, to: Example): Boolean =
        examples.posNoSubexprs.all { ex -> substitutions(ex, from, to).all { valid(it) } } &&
                examples.neg.all { ex -> substitutions(ex, from, to).all { minimalNegative(it) } }

    override fun dummy(e: Example): Int {
        if (!valid(e)) throw Exception("Failed oracle precondition")
        val i = representatives.indexOfFirst { equal(it, e) }
        if (i != -1) return i
        representatives.add(e)
        return representatives.size - 1
    }
}

/**
 * Every way to replace a nonempty set of occurrences of [from] in [ex] with [to]. No occurrence of
 * [from] can contain another, so the occurrences are disjoint.
 */
fun substitutions(ex: Example, from: Example, to: Example): Sequence<Example> {
    val n = occurrences(ex, from)
    require(n < Int.SIZE_BITS - 1) { "Too many occurrences of $from in $ex" }
    return (1 until (1 shl n)).asSequence().map { mask -> replace(ex, from, to, mask, Counter()) }
}

private fun occurrences(ex: Example, target: Example): Int =
    when {
        ex == target -> 1
        ex is App -> occurrences(ex.fn, target) + occurrences(ex.arg, target)
        else -> 0
    }

/** Replace the occurrences of [from] whose index, in left-to-right order, is set in [mask]. */
private fun replace(ex: Example, from: Example, to: Example, mask: Int, index: Counter): Example =
    when {
        ex == from -> if (mask and (1 shl index.get()) != 0) to else ex
        ex is App -> App(replace(ex.fn, from, to, mask, index), replace(ex.arg, from, to, mask, index))
        else -> ex
    }
