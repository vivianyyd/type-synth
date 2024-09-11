package util

import kotlin.reflect.KClass
import kotlin.reflect.KFunction

data class Example(
    val inputs: List<Any>,
    val output: Any
) {
    val args = inputs + listOf(output)
}

data class Type(
    val inputs: List<KClass<*>>,
    val output: KClass<*>
)

data class Func(
    val f: KFunction<Any>?,
    val type: Type,
    val posExamples: List<Example>,
    val negExamples: List<Example>,  // must still be valid types TODO testing: check if we can get expressive examples just with the same inputs but diff outputs. or do the inputs need to be diff
) {
    val examples = posExamples + negExamples
    lateinit var argsWithUndefinedLength: Set<Int>

    fun withNegExample(neg: Example) = Func(f, type, posExamples, negExamples + listOf(neg))
}

data class Query(
    val functions: List<Func>,
    val uImpl: UPrimImpl
) {
    val lens: Map<Any, Int>

    init {
        functions.forEach {
            assert(checkFn(it.f, it.type))
            assert(it.examples.all { ex -> checkEx(ex, it.type) })
        }

        // Construct map of lengths and confirm that they were successfully computed
        lens = mutableMapOf()
        functions.forEach {
            val undefLen = mutableSetOf<Int>()
            it.examples.forEach { ex ->
                (ex.inputs + listOf(ex.output)).mapIndexed { i, it ->
                    try {
                        lens[it] = uImpl.len(it)
                    } catch (_: Exception) {
                        val param = if (i == ex.inputs.size) -1 else i
                        undefLen.add(param)
                    }
                }
            }
            it.argsWithUndefinedLength = undefLen
        }
    }

    fun replace(oldF: Func, newF: Func) = Query(functions.filter { it != oldF } + listOf(newF), uImpl)
}

fun checkEx(example: Example, type: Type): Boolean {
    val correctArity = example.inputs.size == type.inputs.size
    val correctTypes =
        (example.inputs + listOf(example.output)).zip(type.inputs + listOf(type.output))
            .all { (ex, ty) ->
                ty.isInstance(ex)
            }
    return correctArity && correctTypes
}

fun checkFn(fn: KFunction<Any>?, type: Type): Boolean {
    if(fn == null) return true
    val correctReturnType = type.output == fn.returnType.classifier
    val correctArgTypes =
        type.inputs.zip(fn.parameters.map { p -> p.type.classifier }).all { (expected, actual) ->
            expected == actual
        }
    return correctReturnType && correctArgTypes
}
