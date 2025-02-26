package util

data class Application(val name: String, val arguments: List<Application> = listOf()) {
    override fun toString(): String {
        return "($name${(arguments.joinToString(prefix=" ", separator = " "))})"
    }
}

fun Iterable<Application>.print(positive: Boolean): String =
    this.joinToString("\n") { "(${if (positive) "+" else "-"} $it)" }
