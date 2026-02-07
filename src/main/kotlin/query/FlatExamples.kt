package query

data class FlatApp(val name: String, val args: List<FlatApp> = listOf()) {
    fun depth(): Int = args.maxOfOrNull { it.depth() + 1 } ?: 0

    fun unflatten(): Example {
        if (this.args.isEmpty()) return Name(this.name)
        return App(
            FlatApp(this.name, this.args.dropLast(1)).unflatten(), this.args.last().unflatten()
        )
    }

    override fun toString(): String {
        return if (args.isEmpty()) name else "($name ${(args.joinToString(separator = " "))})"
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
        posExamples
            .fold(setOf<String>()) { acc, ex ->
                fun names(app: FlatApp): Set<String> =
                    app.args.fold(setOf(app.name)) { a, arg -> a + names(arg) }
                acc + names(ex)
            }
            .toList()
}
