import query.*
import types.Assignment
import types.toSExpr
import types.toType
import util.SExpr
import util.SExprParser
import util.writeExamples

private fun Assignment.toSExprStrs() = this.entries.joinToString(separator = "\t") {
    "${SExpr.Lst(listOf(SExpr.Atm(it.key), it.value.toSExpr()))}"
}

fun main() {
    // Generated tests
    val dictput = listOf(
        "(i)", "(b)",
        "(d (i) (b))",
        "(d (b) (i))",
        "(d (i) (i))",
        "(d (b) (b))",
        "(-> (d k v) (-> k (-> v (d k v))))"
    )
    val dictchain = dictput + "(-> (d a b) (-> (d b c) (d a c)))"
    val small = listOf("(i)", "(b)", "(-> a (-> b a))")

    val (query, context) = generate(dictchain)
    val generatedExs =
        (sexpsFromExamples(query.posExamples, true) + sexpsFromExamples(query.negExamples, false))
            .joinToString(separator = "\n")
//            .replace("0", "i")
//            .replace("1", "b")
//            .replace("2", "dii")
//            .replace("3", "dbi")
//            .replace("4", "dib")
//            .replace("5", "dbb")
//            .replace("6", "put")
//            .replace("7", "chain")
    writeExamples("${context.toSExprStrs()}\n$generatedExs", "dictchain")
}

fun generate(types: List<String>): Pair<Query, Assignment> {
    val (query, context) = ExampleGenerator(1,
        2,
        200,
        types.map { SExprParser(it).parse().toType() }).examples()
    println("Context:")
    println(context.toList().joinToString(separator = "\n"))
    println("Positive examples: ${query.posExamples.size}")
    println(printInvertDummies(query.posExamples.map { it.flatten() }, context))
    println("Negative examples: ${query.negExamples.size}")
    return query to context
}
