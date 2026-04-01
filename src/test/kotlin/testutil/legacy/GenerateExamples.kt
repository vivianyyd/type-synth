package testutil

import products.ExampleGenerator
import products.types.*
import products.types.Function
import query.FlatApp

fun Assignment.toSExprStrs() =
    this.entries.joinToString(separator = "\t") {
        "${SExpr.Lst(listOf(SExpr.Atm(it.key), it.value.toSExpr()))}"
    }

fun main() {
    val groundTruth =
        listOf(
            "(i)",
            "(b)",
            "(d (i) (b))",
            "(d (b) (i))",
            "(d (i) (i))",
            "(d (b) (b))",
            "(-> (d k v) (-> k (-> v (d k v))))")

    val (query, context) =
        ExampleGenerator(1, 2, 200, groundTruth.map { parseSExpr(it).toProductType() to null })
            .examples()
    println(context.toList().joinToString(separator = "\n"))
    println("Positive examples:")
    println(query.posWithSubexprs.size)
    println(printInvertDummies(query.posWithSubexprs.map { it.flatten() }, context))
    println(query.neg.size)
}

fun printInvertDummies(exs: Collection<FlatApp>, context: Assignment): String {
    fun replaceDummiesWithTypeString(app: FlatApp): FlatApp =
        FlatApp(
            if (app.args.isEmpty()) "${context[app.name]}" else "(${context[app.name]}). ",
            app.args.map { replaceDummiesWithTypeString(it) })
    return exs.map { replaceDummiesWithTypeString(it) }.joinToString(separator = "\n")
}

fun SExpr.toProductType(): Type =
    when (this) {
        is SExpr.Atm -> {
            assert(this.value != "->")
            Variable(this.value)
        }
        is SExpr.Lst -> {
            assert(this.elements.isNotEmpty())
            assert(this.elements[0] is SExpr.Atm)
            val fst = this.elements[0] as SExpr.Atm
            if (fst.value == "->") {
                assert(this.elements.size == 3)
                Function(
                    left = this.elements[1].toProductType(),
                    rite = this.elements[2].toProductType())
            } else {
                LabelNode(
                    label = fst.value, params = this.elements.drop(1).map { it.toProductType() })
            }
        }
    }

fun parseProductType(s: String) = parseSExpr(s).toProductType()

fun Type.toSExpr(): SExpr =
    when (this) {
        is Function -> SExpr.Lst(listOf(SExpr.Atm("->"), left.toSExpr(), rite.toSExpr()))
        is LabelNode -> SExpr.Lst(listOf(SExpr.Atm(label)) + params.map { it.toSExpr() })
        is Variable -> SExpr.Atm(id)
        is Error,
        is TypeHole -> throw Exception("Unsupported Type to SExpr")
    }

/*
Function (-> left rite)
Variable a
Label (l a b c), primitive (l)
 */
