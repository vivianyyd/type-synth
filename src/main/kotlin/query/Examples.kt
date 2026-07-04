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
 *
 * @requires [negIn] contains MINIMAL negative examples, i.e. no strict subexpression is a negative example.
 */
class Examples(posIn: Collection<Example>, negIn: Collection<Example>) {
    val posNoSubexprs: MutableList<Example>
    val neg: MutableList<Example> = negIn.toMutableList()

    init {
        val posInSet = posIn.toSet()
        val strictSubexprs = buildSet {
            // subexprs() ends with the ex itself
            posInSet.forEach { addAll(it.subexprs().dropLast(1)) }
        }
        posNoSubexprs = posInSet.filter { it !in strictSubexprs }.toMutableList()
    }

    val posWithSubexprs by lazy {
        buildSet {
            posNoSubexprs.forEach { addAll(it.subexprs()) }
        }.toList()
    }

    val names by lazy {
        buildSet {
            (posNoSubexprs + neg).forEach { addAll(it.names) }
        }.sorted()
    }

    private val flatPos by lazy { flat(posWithSubexprs) }
    private val flatNeg by lazy { flat(neg) }

    fun flatPos(name: String) = flatPos[name] ?: listOf()

    fun flatNeg(name: String) = flatNeg[name] ?: listOf()

    private fun flat(exs: Collection<Example>) = exs.map { it.flatten() }.groupBy { it.name }

    override fun toString() = "Pos\n" + posWithSubexprs.lines() + "\n" + "Neg\n" + neg.lines()
}
