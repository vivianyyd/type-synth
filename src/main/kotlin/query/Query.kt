package query

import java.util.IdentityHashMap

sealed interface Example {
    val names: Set<String>

    fun depth(): Int = flatten().depth()

    fun size(): Int =
        when (this) {
            is Name -> 1
            is App -> fn.size() + arg.size()
        }

    fun flatten(): FlatApp =
        when (this) {
            is Name -> FlatApp(this.name)
            is App -> {
                val flatFn = fn.flatten()
                val flatArg = arg.flatten()
                FlatApp(flatFn.name, flatFn.args + flatArg)
            }
        }

    /**
     * Produce all subexpressions of [this] and [this] TODO for some reason before, I didn't want to
     * include Names? why All subexprs appear in the list before any expression that contains them.
     */
    fun subexprs(): List<Example> =
        LinkedHashSet(
            when (this) {
                is Name -> listOf(this)
                is App -> fn.subexprs() + arg.subexprs() + this
            }
        )
            .toList()
}

data class Name(val name: String) : Example {
    override fun toString() = name

    override val names by lazy { setOf(name) }
}

data class App(val fn: Example, val arg: Example) : Example {
    override fun toString(): String = "$fn ${if (arg is App) "($arg)" else "$arg"}"

    override val names by lazy { fn.names + arg.names }
}

private const val HASH_MULTIPLIER = 31
private const val NAME_TAG = 1
private const val APP_TAG = 2

private data class ExampleCounts(val example: Example, var subtreeCount: Int = 0, var rootCount: Int = 0)

/**
 * Returns only examples that are not proper subexpressions of another example in the collection.
 * This uses bottom-up structural hashing to count subtree and root occurrences, with equality
 * checks inside hash buckets to guard against collisions.
 */
fun filterNonSubexpressions(examples: Collection<Example>): List<Example> {
    if (examples.isEmpty()) return emptyList()
    val exampleList = examples.toList()
    val countsByHash = mutableMapOf<Int, MutableList<ExampleCounts>>()
    val hashCache = IdentityHashMap<Example, Int>()

    fun entryFor(ex: Example, hash: Int): ExampleCounts {
        val bucket = countsByHash.getOrPut(hash) { mutableListOf() }
        val existing = bucket.firstOrNull { it.example == ex }
        if (existing != null) return existing
        return ExampleCounts(ex).also { bucket.add(it) }
    }

    fun computeHash(ex: Example): Int {
        val cached = hashCache[ex]
        if (cached != null) return cached
        val hash =
            when (ex) {
                is Name -> HASH_MULTIPLIER * ex.name.hashCode() + NAME_TAG
                is App -> {
                    val fnHash = computeHash(ex.fn)
                    val argHash = computeHash(ex.arg)
                    HASH_MULTIPLIER * (HASH_MULTIPLIER * fnHash + argHash) + APP_TAG
                }
            }
        hashCache[ex] = hash
        return hash
    }

    fun countSubtrees(ex: Example): Int {
        val hash = computeHash(ex)
        entryFor(ex, hash).subtreeCount++
        when (ex) {
            is Name -> {}
            is App -> {
                countSubtrees(ex.fn)
                countSubtrees(ex.arg)
            }
        }
        return hash
    }

    val rootEntries = exampleList.map { ex ->
        val hash = countSubtrees(ex)
        entryFor(ex, hash).also { it.rootCount++ }
    }

    return rootEntries.mapNotNull { entry ->
        entry.example.takeIf { entry.subtreeCount == entry.rootCount }
    }
}

/**
 * This is more general than the previous query because we can apply the result of applications
 * without them being explicitly assigned to a name [posWithSubexprs] contains all subexpressions!
 */
class Query(pos: Collection<Example> = listOf(), val neg: Collection<Example> = listOf()) {
    val posNoSubexprs: List<Example>

    init {
        posNoSubexprs = filterNonSubexpressions(pos)
    }

    val posWithSubexprs: List<Example> = posNoSubexprs.toSet().flatMap { it.subexprs() }.toSet().toList()
    val names: List<String> =
        pos.fold(setOf<String>()) { acc, ex -> acc + ex.names }.toList().sorted()

    private val flatPos = flat(posNoSubexprs)
    private val flatNeg = flat(neg)

    fun flatPosNoSubexprs(name: String) = flatPos[name] ?: listOf()
    fun flatNeg(name: String) = flatNeg[name] ?: listOf()

    private fun flat(exs: Collection<Example>) = exs.map { it.flatten() }.groupBy { it.name }
}
