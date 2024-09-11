//package step2
//
//import bottomup.BottomUp
//import util.Example
//import util.Query
//import util.Type
//import util.checkEx
//import kotlin.reflect.KFunction
//
//data class Function(val f: KFunction<Any>, val type: Type)
//
//interface Node
//
//data class Application(val f: Query, val args: List<Node>): Node
//data class Input(val index: Int) : Node
//
///**
// * Now that we're done with step 1, it's time for a step 2!
// *
// * Kinda sad this can't be called bottoms up since it's a top-down synthesizer
// */
//class TopDown(private val queries: List<Query>, private val examples: List<Example>) {
//    private val properties = queries.associateWith { BottomUp(it).enumerate() }.filterNotNull()
//    // TODO assert that all UPrimImpls are the same here. Future: Make gigaquery which just contains multiple functions
//    //  and one single UPrimImpl.
//
//    fun enumerate():
//
//    fun Query.satisfiesExamples(examples: List<Example>): Boolean {
//        return examples.all {ex ->
//            properties[this]?.evaluate(ex, this.uImpl) ?: false
//        }
//    }
//
//    fun Query.hasCorrectType(examples: List<Example>): Boolean =
//        examples.all { checkEx(it, this.type) }
//}
//
//fun <K, V> Map<K, V?>.filterNotNull(): Map<K, V> =
//    this.mapNotNull { it.value?.let { value -> it.key to value } }.toMap()
