package core

sealed interface Language

sealed interface CoreType<L : Language>
sealed class TypeConstructor<L : Language>(open val params: List<CoreType<L>>) : CoreType<L>
sealed interface Variable<L : Language> : CoreType<L>

data class Arrow<L : Language> private constructor(override val params: List<CoreType<L>>) :
    TypeConstructor<L>(params) {
    constructor(l: CoreType<L>, r: CoreType<L>) : this(mutableListOf(l, r))

    override fun toString(): String = "${if (params[0] is Arrow) "(${params[0]})" else "${params[0]}"} -> ${params[1]}"
}

//object Init : Language
//object InitVariable : Variable<Init>
//object InitLabel : TypeConstructor<Init>(listOf())
//
//fun main() {
//    val a = Arrow(InitVariable, InitLabel)
//}
