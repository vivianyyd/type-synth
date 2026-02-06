import products.ExampleGenerator
import products.types.Assignment
import products.types.Type
import products.types.toSExpr
import products.types.toType
import query.Query
import util.io.SExpr
import util.io.parseSExpr

fun Assignment.toSExprStrs() =
    this.entries.joinToString(separator = "\t") {
        "${SExpr.Lst(listOf(SExpr.Atm(it.key), it.value.toSExpr()))}"
    }

fun generate(types: List<Pair<Type, String?>>): Pair<Query, Assignment> {
    val (query, context) = ExampleGenerator(1, 2, 500, types).examples()
    println("Positive examples: ${query.posWithSubexprs.size}")
    println("Negative examples: ${query.neg.size}")
    return query to context
}

fun generateFromSExpr(types: List<Pair<String, String?>>): Pair<Query, Assignment> =
    generate(types.map { parseSExpr(it.first).toType() to it.second })
