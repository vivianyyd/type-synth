package sketchral

import util.Example
import util.Func

sealed class Result {
    class Ok(val value: String) : Result()
    object Error : Result()
}

class OutputParser(val output: String, val inputFactory: InputFactory) {
    private val numInputs = inputFactory.function.type.inputs.size
    private fun paramToName(param: Int) = if (param == numInputs) "o" else "x$param"

    private fun blockOfSignature(sig: String): List<String> {
        var txt = output.substringAfterLast("$sig (")
        txt = txt.substringAfter('{')
        txt = txt.substringBefore('}')
        return txt.split(';').map { it.trim() }
    }

    fun parseProperty(): Result {
        val lines = blockOfSignature("void property")
        val lenStoreToName = lines.filter { "length" in it }.associate {
            var line = it.substringAfter('(')  // "parameter, variable_len_stored_in)"
            val variable = line.substringBefore(',')
            line = line.substringAfter(',')
            val storedLen = line.substringBefore(')').trim()
            storedLen to variable
        }.toSortedMap(reverseOrder())  // natural order puts short strings first, but we want to replace substrings last
        var property = lines.find { "out =" in it }?.substringAfter("out =")?.trim() ?: return Result.Error
        lenStoreToName.forEach { (lenStore, name) -> property = property.replace(lenStore, "length($name)")}
        return Result.Ok("$property;")
    }

    fun getLams(): Lambdas {
        TODO()
    }

    fun parsePosEx(): Example {
        TODO()
    }

    fun parseNegExPrecision(): Example {
        val lines = blockOfSignature("void negative_example")
        val line = lines.first { "get_ex" in it }.substringAfter('(')
        val t = line.substringBefore(',').toInt()
        val outDummy = lines.find{ "o =" in it}?.substringAfter("o =")?.trim()?.toInt() ?:throw Exception("I'm sad")
        return Example(
            inputFactory.function.posExamples[t].inputs,
            inputFactory.dummyToArg[outDummy]!!
        )
    }

    fun parseMaxsat(neg_may: List<Example>): Pair<List<Example>, List<Example>> {
        TODO()
    }
}