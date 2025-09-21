package core

sealed interface Language

sealed interface CoreType<L : Language>
sealed interface TypeConstructor<L : Language> : CoreType<L>
sealed interface Variable<L : Language> : CoreType<L>
data class Arrow<L : Language>(val l: CoreType<L>, val r: CoreType<L>) : TypeConstructor<L> {
    override fun toString(): String = "${if (l is Arrow) "($l)" else "$l"} -> $r"
}

object Init : Language
object InitVariable : Variable<Init>
object InitLabel : TypeConstructor<Init>

fun main() {
    val a = Arrow(InitVariable, InitLabel)
}
