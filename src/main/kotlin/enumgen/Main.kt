package enumgen

fun main() {
    val integer = Application("0", null)
    val f = Application("f", listOf(integer))
    val bool = Application("t", null)

    val e = Enumerator(listOf("0", "f", "t"), setOf(integer, f, bool), setOf(Application("f", listOf(bool))), 0)
    println("result: ${e.enumerate()}")
}
