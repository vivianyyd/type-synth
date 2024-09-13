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
    val numArgs: Int,
    val posExamples: List<Example>,
    val negExamples: List<Example>,  // must still be valid types TODO testing: check if we can get expressive examples just with the same inputs but diff outputs. or do the inputs need to be diff
) {
    val examples = posExamples + negExamples
    lateinit var argsWithUndefinedLength: Set<Int>

    fun withNegExample(neg: Example) = Func(f, numArgs, posExamples, negExamples + listOf(neg))
}

data class Query(
    val functions: List<Func>,
) {

    fun replace(oldF: Func, newF: Func) = Query(functions.filter { it != oldF } + listOf(newF))
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
