package query

/**
 * A name applied to arguments, as [Example.flatten] makes it. The arguments are whole examples, so
 * an argument may be a lambda or a let.
 */
data class FlatApp(val name: String, val args: List<Example> = listOf()) {
    fun depth(): Int = args.maxOfOrNull { it.depth() + 1 } ?: 0

    fun unflatten(): Example = args.fold(Name(name) as Example) { fn, arg -> App(fn, arg) }

    override fun toString(): String {
        if (args.isEmpty()) return name
        return "($name ${args.joinToString(separator = " ") { if (it is Name) "$it" else "($it)" }})"
    }
}

fun Iterable<FlatApp>.print(positive: Boolean): String =
    this.joinToString("\n") { "(${if (positive) "+" else "-"} $it)" }

class FlatExamples(
    posExamples: Collection<FlatApp> = listOf(),
    val negExamples: Collection<FlatApp> = listOf(),
    names: List<String> = listOf()
) {
    val posExamples: Set<FlatApp> = (posExamples.toSet() + names.map { FlatApp(it) }.toSet())
    val names: List<String> =
        posExamples.flatMap { it.unflatten().names }.distinct()
}
