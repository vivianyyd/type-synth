package examplegen

import enumgen.Assignment
import enumgen.types.*
import enumgen.types.Function
import util.FlatApp
import util.FlatQuery
import util.SExprParser
import util.reflexiveNaryProduct
import java.util.*

class ExampleGenerator(
    private val MAX_TYPE_DEPTH: Int,
    private val MAX_DEPTH: Int,  // todo assert this is at least the max depth of any parameter type!
    private val ERROR_COVERAGE_CAPACITY: Int,
    private val fns: List<Type>
) {
    private var name = 0
    private fun freshValue() = "${name++}"

    /**
     * A type is observable as long as it is a function, or
     * it is *not* only ever seen as the output of a function.
     * For now, we unwrap functions to get arguments, but we don't include results of partial application to avoid blowup.
     */
    private fun observableNonFunctionTypes(): List<Type> {
        val obs = mutableListOf<Type>()
        fns.forEach {
            when (it) {
                is Function -> {
                    fun args(f: Function): List<Type> =
                        listOf(f.left) + (if (f.rite is Function) args(f.rite) else listOf())
                    obs.addAll(listOf(it) + args(it))
                }
                is Variable, is LabelNode -> obs.add(it)
                is TypeHole, is Error -> throw Exception("no way")
            }
        }
        return obs
    }

    /**
     * Explode the abstract (contain variables) labelled types into concrete types and give them dummies
     * Not doing anything with functions for now.
     */
    // todo abstract isn't the right word to describe the above but whatever
    private fun dummies(ts: List<Type>): Map<String, Type> {
        val (primitives, parameterized) = ts.filterIsInstance<LabelNode>().partition { it.params.isEmpty() }
        val typesWithDummies = primitives.associateWith { 0 }.toMutableMap()
        // Explode label nodes
        for (d in 1..MAX_TYPE_DEPTH) {
            for (label in parameterized) {
                val paramAssignments = reflexiveNaryProduct(
                    typesWithDummies.filter { (_, v) -> v + 1 <= d }.keys.toList(),
                    label.params.size
                )
                for (args in paramAssignments) {
                    val ty = LabelNode(label.label, args)
                    if (ty !in typesWithDummies) typesWithDummies.put(ty, d)
                }
            }
        }
        return typesWithDummies.keys.associateBy { freshValue() }
    }

    fun examples(): Pair<FlatQuery, Assignment> {
        if (fns.isEmpty()) return Pair(FlatQuery(), mapOf())

        val dummies = dummies(observableNonFunctionTypes()).toMutableMap()
        val posExamples = dummies.keys.map { FlatApp(it) }.toMutableSet()
        val negExs: MutableMap<ErrorCategory, MutableSet<FlatApp>> =
            EnumMap(ErrorCategory.values().associateWith { mutableSetOf() })
        // We don't want functions to show up in examples for now TODO no HOF..., but we want to give them names
        val fnDummies = fns.filterIsInstance<Function>().associateBy { freshValue() }
        dummies.putAll(fnDummies)

        // BEGIN COMPOSITION LOOP
        for (i in 1..MAX_DEPTH) {
            for (ty in fns.filter { it.numParams() > 0 }) {
                val name = dummies.filter { (_, t) -> t == ty }.map { (name, _) -> name }[0]
                // TODO Bug: We generate many of the smaller examples multiple times. Instead of calling product in a loop,
                //   we should be doing bottom up enumeration if that makes sense idk
                var apps =  // If we make new examples from only positive ones, any errors won't be redundant!
                    reflexiveNaryProduct(posExamples.toList(), ty.numParams()).map { argChoice ->
                        FlatApp(
                            name,
                            argChoice
                        )
                    }
                // Don't modify posExamples in the loop, since we loop over apps which is generated from posExamples
                val posExsTmp = mutableSetOf<FlatApp>()
                while (apps.any() /*&& negExs.any { (_, v) -> v.size < ERROR_COVERAGE_CAPACITY } we want exhaustive list of posexs*/) {
                    val example = apps.first()
                    apps = apps.drop(1)

                    val eval = checkApplication(example, dummies)
                    if (eval is Error) {
                        if (negExs[eval.category]!!.size < ERROR_COVERAGE_CAPACITY)
                            negExs[eval.category]!!.add(example)
                    } else {
                        posExsTmp.add(example)
                    }
                }
                posExamples.addAll(posExsTmp)
                // TODO we can purposefully add some negative examples where we apply too many arguments, although
                //  it shouldn't be necessary
            }
        }
        posExamples.addAll(fnDummies.keys.map { FlatApp(it) })
        return Pair(FlatQuery(posExamples, negExs.values.flatten().toSet()), dummies)
    }
    // TODO Very good to have negexs where the first args are ok but latter ones don't bc of var mismatch or something.
    //   Instead of keeping all exs, we could throw away some if we have >5 for that error type for that fn name already!
    //   TODO generator style will work here
}

fun main() {
    val groundTruth = listOf("(i)", "(b)", "(-> a (-> (l a) (l a)))")

    val (query, context) = ExampleGenerator(
        2,
        2,
        30,
        groundTruth.map { tySexpr -> SExprParser(tySexpr).parse().toType() }).examples()
    println(context.toList().joinToString(separator = "\n"))
    println("Positive examples:")
    println(query.posExamples.size)
    println(printInvertDummies(query.posExamples, context))
    println(query.negExamples.size)
}

private fun printInvertDummies(exs: Collection<FlatApp>, context: Assignment): String {
    fun replaceDummiesWithTypeString(app: FlatApp): FlatApp =
        FlatApp("(${context[app.name]}). ", app.args.map { replaceDummiesWithTypeString(it) })
    return exs.map { replaceDummiesWithTypeString(it) }.joinToString(separator = "\n")
}