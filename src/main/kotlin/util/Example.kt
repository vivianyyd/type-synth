package util

/**
 * If [arguments] is null, the function [name] is not applied.
 *
 * Later: If [arguments] is empty, [name] is applied with no arguments. For now, unit doesn't exist, all fn must have an
 * argument to be applied, this is WLOG since we can just have a unit value be passed
 * TODO idk wtf the above comment is saying, let's use ocaml model of no such thing as applying function with no
 *  arguments, need to apply with unit. Is this WLOG?
 */
data class Application(val name: String, val arguments: List<Application>?) {
    override fun toString(): String {
        return if (arguments == null) name else
            "($name ${(arguments.joinToString(separator = " ") ?: "")})"
    }
}

fun Iterable<Application>.print(positive: Boolean): String =
    this.joinToString("\n") { "(${if (positive) "+" else "-"} $it)" }
