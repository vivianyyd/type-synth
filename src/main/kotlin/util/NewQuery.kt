package util

sealed interface Example
data class Name(val name: String) : Example {
    override fun toString() = name
}

data class App(val fn: Example, val arg: Example) : Example {
    override fun toString(): String = "$fn ${if (arg is App) "($arg)" else "$arg"}"
}

/**
 * This is more general than the previous query because we can apply the result of applications
 *  without them being explicitly assigned to a name
 *  [posExamples] contains all subexpressions!
 *  */
class NewQuery(
    posExamples: Collection<Example> = listOf(),
    val negExamples: Collection<Example> = listOf(),
    names: List<String> = listOf()
) {
    val posExamples: Set<Example> =
        (posExamples.toSet() + names.map { Name(it) }.toSet()).flatMap { it.subexprs() }.toSet()
    val names: List<String> = names.union(posExamples.fold(setOf()) { acc, ex ->
        fun names(ex: Example): Set<String> = when (ex) {
            is Name -> setOf(ex.name)
            is App -> names(ex.fn) + names(ex.arg)
        }
        acc + names(ex)
    }).toList()
}

/** Produce all subexpressions of [this] and [this], except values.
 * All subexprs appear in the list before any expression that contains them. */
private fun Example.subexprs(): List<App> = LinkedHashSet(
    when (this) {
        is Name -> listOf()
        is App -> fn.subexprs() + arg.subexprs() + this
    }
).toList()
