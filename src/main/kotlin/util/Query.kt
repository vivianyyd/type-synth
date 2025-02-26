package util

data class Application(val name: String, val arguments: List<Application> = listOf()) {
    override fun toString(): String {
        return if (arguments.isEmpty()) name else
            "($name ${(arguments.joinToString(separator = " "))})"
    }
}

fun Iterable<Application>.print(positive: Boolean): String =
    this.joinToString("\n") { "(${if (positive) "+" else "-"} $it)" }

class Query(
    posExamples: Collection<Application> = listOf(),
    val negExamples: Collection<Application> = listOf(),
    names: List<String> = listOf()
) {
    val posExamples: Set<Application> = (posExamples.toSet() + names.map { Application(it) }.toSet())
    val names: List<String> = posExamples.fold(setOf<String>()) { acc, ex ->
        fun names(app: Application): Set<String> = app.arguments.fold(setOf(app.name)) { a, arg -> a + names(arg) }
        acc + names(ex)
    }.toList()
}
