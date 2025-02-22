package examplegen

import enumgen.Assignment
import util.Application
import util.reflexiveNaryProduct
import enumgen.types.*
import enumgen.types.Function
import util.SExprParser
import util.upToNaryCartesianProduct

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

    private fun explode(fns: List<Type>): Pair<List<Application>, Assignment> {
        if (fns.isEmpty()) return Pair(listOf(), mapOf())
        val examples = mutableListOf<Application>()

        val dummies = dummies(observableNonFunctionTypes(fns)).toMutableMap()
        examples.addAll(dummies.keys.map { Application(it, null) })
        // We don't want functions to show up in examples for now TODO no HOF..., but we want to give them names
        val fnDummies = fns.filterIsInstance<Function>().associateBy { freshValue() }
        dummies.putAll(fnDummies)

        // BEGIN COMPOSITION LOOP
        for (i in 0..MAX_DEPTH) {
            val args = upToNaryCartesianProduct(examples, fns.maxOf { it.numParams() })
            fns.filter { it.numParams() > 0 }.forEach { ty ->
                val name = dummies.filter { (_, t) -> t == ty }.map { (name, _) -> name }[0]
                examples.addAll(args[ty.numParams() - 1].map { argChoice -> Application(name, argChoice) })
                // TODO we can purposefully add some negative examples where we apply too many arguments, although
                //  it shouldn't be necessary
            }
        }
        examples.addAll(fnDummies.keys.map { Application(it, null) })
        return Pair(examples, dummies)
    }

    fun examples(fns: List<Type>): Pair<Pair<List<Application>, List<Application>>, Assignment> {
        val (exs, context) = explode(fns)
        return Pair(exs.partition { checkApplication(it, context) !is Error }, context)
        // TODO Very good to have negexs where the first args are ok but latter ones don't bc of var mismatch or something.
        //   Instead of keeping all exs, we could throw away some if we have >5 for that error type for that fn name already!
        //   TODO generator style will work here
    }

    private val MAX_DEPTH = 1  // todo assert this is at least the max depth of any parameter type!
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

    val ex = ExampleGenerator.examples(groundTruth.map { tySexpr -> SExprParser(tySexpr).parse().toType() })
    println(ex.second.toList().joinToString(separator="\n"))
    println(ex.first.first.size)
    println(ex.first.second.size)
    /*
    Function (-> left rite)
    Variable a
    Label (l a b c), primitive (l)
     */

}