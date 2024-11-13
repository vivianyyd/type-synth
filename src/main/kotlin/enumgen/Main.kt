package enumgen

fun main() {
    val integer = Application("int", null)
    val f = Application("f", listOf(integer))
    val bool = Application("bool", null)

    val e = Enumerator(listOf("int", "f", "bool"), setOf(integer, f, bool), setOf(Application("f", listOf(bool))), 0)
    println("result: ${e.enumerate()}")
}
/*

/**
 * If [arguments] is null, the function [name] is not applied.
 *
 * Later: If [arguments] is empty, [name] is applied with no arguments. For now, unit doesn't exist, all fn must have an
 * argument to be applied, this is WLOG since we can just have a unit value be passed
 */
data class Application(val name: String, val arguments: List<Application>?)

 */