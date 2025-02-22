package examplegen

import enumgen.Assignment
import util.Application
import util.reflexiveNaryProduct
import enumgen.types.*
import enumgen.types.Function
import util.SExprParser
import java.util.*

object ExampleGenerator {
    private var name = 0
    private fun freshValue() = "${name++}"

    /**
     * A type is observable as long as it is a function, or
     * it is *not* only ever seen as the output of a function.
     * For now, we unwrap functions to get arguments, but we don't include results of partial application to avoid blowup.
     */
    private fun observableNonFunctionTypes(ts: Collection<Type>): List<Type> {
        val obs = mutableListOf<Type>()
        ts.forEach {
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
        val typesWithDummies = primitives.toMutableSet()
        // Explode label nodes
        for (d in 1..MAX_DEPTH) {
            for (label in parameterized) {
                val paramAssignments = reflexiveNaryProduct(typesWithDummies.toList(), label.params.size)
                for (args in paramAssignments) {
                    typesWithDummies.add(LabelNode(label.label, args))
                }
            }
        }
        return typesWithDummies.associateBy { freshValue() }
    }

    fun examples(fns: List<Type>): Triple<List<Application>, List<Application>, Assignment> {
        if (fns.isEmpty()) return Triple(listOf(), listOf(), mapOf())

        val dummies = dummies(observableNonFunctionTypes(fns)).toMutableMap()
        val posExamples = dummies.keys.map { Application(it, null) }.toMutableList()
        val negExamples = mutableListOf<Application>()
        // We don't want functions to show up in examples for now TODO no HOF..., but we want to give them names
        val fnDummies = fns.filterIsInstance<Function>().associateBy { freshValue() }
        dummies.putAll(fnDummies)

        // BEGIN COMPOSITION LOOP
        for (i in 0..MAX_DEPTH) {
            for (ty in fns.filter { it.numParams() > 0 }) {
                val name = dummies.filter { (_, t) -> t == ty }.map { (name, _) -> name }[0]
                var apps =  // If we make new examples from only positive ones, any errors won't be redundant!
                    reflexiveNaryProduct(posExamples, ty.numParams()).map { argChoice -> Application(name, argChoice) }

                val negExs: MutableMap<ErrorCategory, MutableList<Application>> =
                    EnumMap(ErrorCategory.values().associateWith { mutableListOf() })
                while (apps.any() && negExs.any { (_, v) -> v.size < ERROR_COVERAGE_CAPACITY }) {
                    val example = apps.first()
                    apps = apps.drop(1)

                    println(example)

                    val eval = checkApplication(example, dummies)
                    if (eval is Error) {
                        if (negExs[eval.category]!!.size < ERROR_COVERAGE_CAPACITY)
                            negExs[eval.category]!!.add(example)
                    }
                    else {
                        posExamples.add(example)
                    }
                }
                negExamples.addAll(negExs.values.flatten())
                // TODO we can purposefully add some negative examples where we apply too many arguments, although
                //  it shouldn't be necessary
            }
        }
        posExamples.addAll(fnDummies.keys.map { Application(it, null) })
        return Triple(posExamples, negExamples, dummies)
    }
        // TODO Very good to have negexs where the first args are ok but latter ones don't bc of var mismatch or something.
        //   Instead of keeping all exs, we could throw away some if we have >5 for that error type for that fn name already!
        //   TODO generator style will work here

    private val MAX_DEPTH = 1  // todo assert this is at least the max depth of any parameter type!
    private val ERROR_COVERAGE_CAPACITY = 10
}

fun main() {
    val groundTruth = listOf(
        "(int)",
        "(bool)",
        "(l (int))",
        "(l (bool))",
//        "(l (l (int)))",  // TODO no idea why, but adding this also causes us to add longer bool list too not just int
        "(-> a (-> (l a) (l a)))"
    )

    val (pos, neg, context) = ExampleGenerator.examples(groundTruth.map { tySexpr -> SExprParser(tySexpr).parse().toType() })
    println(context.toList().joinToString(separator = "\n"))
    println(pos.size)
    println(neg.size)
    /*
    Function (-> left rite)
    Variable a
    Label (l a b c), primitive (l)
     */

}