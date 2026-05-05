package query

import util.lines

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

/**
 * This is more general than the previous query because we can apply the result of applications
 * without them being explicitly assigned to a name [posWithSubexprs] contains all subexpressions!
 */
class Examples(pos: Collection<Example>, val neg: Collection<Example>) {
    val posNoSubexprs: List<Example>

    init {
        // TODO this is not quite right since examples are not flattened.
        //   instead, we should flatten and eliminate prefixes.
        val noSubexprs = pos.toMutableList()
        for (posEx in pos) {
            when (posEx) {
                is Name -> noSubexprs.removeAll { it == posEx }
                is App -> noSubexprs.removeAll { it == posEx.fn || it == posEx.arg }
            }
        }
        posNoSubexprs = noSubexprs
    }

    val posWithSubexprs: List<Example> =
        posNoSubexprs.toSet().flatMap { it.subexprs() }.toSet().toList()
    val names: List<String> =
        (pos + neg).fold(setOf<String>()) { acc, ex -> acc + ex.names }.toList().sorted()

    private val flatPos = flat(posWithSubexprs)
    private val flatNeg = flat(neg)

    fun flatPos(name: String) = flatPos[name] ?: listOf()

    fun flatNeg(name: String) = flatNeg[name] ?: listOf()

    private fun flat(exs: Collection<Example>) = exs.map { it.flatten() }.groupBy { it.name }

    override fun toString() = "Pos\n" + posWithSubexprs.lines() + "\n" + "Neg\n" + neg.lines()
}
