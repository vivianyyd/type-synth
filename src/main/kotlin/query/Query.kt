package query

sealed interface Example {
    val names: Set<String>
}

data class Name(val name: String) : Example {
    override fun toString() = name
    override val names by lazy { setOf(name) }
}

data class App(val fn: Example, val arg: Example) : Example {
    override fun toString(): String = "$fn ${if (arg is App) "($arg)" else "$arg"}"
    override val names by lazy { fn.names + arg.names }
}

fun Example.depth(): Int = this.flatten().depth()

fun FlatApp.depth(): Int = args.maxOfOrNull { it.depth() + 1 } ?: 0

fun Example.size(): Int = when (this) {
    is Name -> 1
    is App -> fn.size() + arg.size()
}

fun Example.flatten(): FlatApp = when (this) {
    is Name -> FlatApp(this.name)
    is App -> {
        val flatFn = fn.flatten()
        val flatArg = arg.flatten()
        FlatApp(flatFn.name, flatFn.args + flatArg)
    }
}

fun FlatApp.unflatten(): Example {
    if (this.args.isEmpty()) return Name(this.name)
    return App(
        FlatApp(this.name, this.args.dropLast(1)).unflatten(),
        this.args.last().unflatten()
    )
}

/**
 * This is more general than the previous query because we can apply the result of applications
 *  without them being explicitly assigned to a name
 *  [posExamples] contains all subexpressions!
 *  */
class Query(
    posExamples: Collection<Example> = listOf(),
    val negExamples: Collection<Example> = listOf(),
    names: List<String> = listOf(),
    includesSubexprs: Boolean = false
) {
    val posExsBeforeSubexprs: List<Example>

    init {
        val noSubexprs = posExamples.toMutableList()
        for (pos in posExamples) {
            when (pos) {
                is Name -> noSubexprs.removeAll { it == pos }
                is App -> noSubexprs.removeAll { it == pos.fn || it == pos.arg }
            }
        }
        posExsBeforeSubexprs = noSubexprs
    }

    val posExamples: Set<Example> = (posExamples + names.map { Name(it) }).toSet()
        .let { if (includesSubexprs) it else it.flatMap { it.subexprs() }.toSet() }
    val names: List<String> = names.union(posExamples.fold(setOf()) { acc, ex -> acc + ex.names }).toList().sorted()
}

/** Produce all subexpressions of [this] and [this] TODO for some reason before, I didn't want to include Names? why
 * All subexprs appear in the list before any expression that contains them. */
private fun Example.subexprs(): List<Example> = LinkedHashSet(
    when (this) {
        is Name -> listOf(this)
        is App -> fn.subexprs() + arg.subexprs() + this
    }
).toList()
