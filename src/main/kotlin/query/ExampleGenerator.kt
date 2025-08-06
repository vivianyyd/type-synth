package query

import types.*
import types.Function
import util.SExprParser
import util.reflexiveNaryProduct
import java.util.*

class ExampleGenerator(
    private val MAX_TYPE_DEPTH: Int,
    private val MAX_DEPTH: Int,  // todo assert this is at least the max depth of any parameter type!
    private val ERROR_COVERAGE_CAPACITY: Int,
    private val namedFns: List<Pair<Type, String?>>
) {
    private var name = 0
    private fun freshValue() = "${name++}"
    private val fns = namedFns.map { it.first }

    /**
     * A type is observable as long as it is a function, or it is *not* only ever seen as the output of a function.
     * We unwrap functions to get arguments, but we don't include results of partial application to avoid blowup.
     */
    private val observableNonFunctionTypes: List<Type> = fns.fold(listOf()) { a, it ->
        when (it) {
            is Function -> {
                fun args(f: Function): List<Type> =
                    listOf(f.left) + (if (f.rite is Function) args(f.rite) else listOf())
                a + listOf(it) + args(it)
            }
            is Variable, is LabelNode -> a + it
            is TypeHole, is Error -> throw Exception("no way")
        }
    }

    fun examples(): Pair<Query, Assignment> {
        if (fns.isEmpty()) return Pair(Query(), mapOf())

        // Explode parameterized labelled types into concrete types and give them dummies, skip functions for now
        val (primitives, parameterized) = observableNonFunctionTypes.filterIsInstance<LabelNode>()
            .partition { it.params.isEmpty() }
        val typeAndDepth = primitives.associateWith { 0 }.toMutableMap()
        // Explode label nodes
        for (d in 1..MAX_TYPE_DEPTH) {
            for (label in parameterized) {
                // TODO Bug: We generate small examples many times - we want to product big new exprs w small ones,
                //  so we keep smaller ones in the pool, but then we frequently make products which only contain small ones
                //  need to enforce output is SxSx...xS - sxsx...xs where s subset S.
                //  Solution: doesn't matter until last index, at which point if we've only picked from s we can only pick S.
                val paramAssignments = reflexiveNaryProduct(
                    typeAndDepth.filter { (_, v) -> v + 1 <= d }.keys.toList(), label.params.size
                )
                for (args in paramAssignments) {
                    val ty = LabelNode(label.label, args)
                    if (ty !in typeAndDepth) typeAndDepth[ty] = d
                }
            }
        }
        val nonFnDummies = typeAndDepth.keys.associateBy { freshValue() }
        val fnDummies = fns.filterIsInstance<Function>().associateBy { freshValue() }
        val dummies = nonFnDummies + fnDummies

        // We don't want functions to be subexprs in expressions yet, so only add nonFns when initializing posExamples
        //  fn dummies are added as positive examples at the end
        //  TODO Need to change this to support HOFs
        val posExamples = mutableMapOf<Type, MutableList<Example>>()

        fun addPos(t: Type, ex: Example) {
            if (t in posExamples) posExamples[t]!!.add(ex) else posExamples[t] = mutableListOf(ex)
        }
        nonFnDummies.forEach { (n, t) -> addPos(t, Name(n) as Example) }
        val negExamples = EnumMap(ErrorCategory.values().associateWith { mutableSetOf<Example>() })

        fun addNeg(err: ErrorCategory, ex: Example) {
            if (err in negExamples) {
                if (negExamples[err]!!.size < ERROR_COVERAGE_CAPACITY) negExamples[err]!!.add(ex)
            } else negExamples[err] = mutableSetOf(ex)
        }
        // BEGIN COMPOSITION LOOP
        for (i in 1..MAX_DEPTH) {
            dummies.filter { it.value is Function }.forEach { (name, dummyTy) ->
                val inProgress: MutableList<Pair<Example, Function>> = mutableListOf(Name(name) to dummyTy as Function)
                while (inProgress.isNotEmpty()) {
                    val (currEx, currTy) = inProgress.removeFirst()

                    val (goodArgs, badArgs) = posExamples.entries.associate { (t, exs) ->
                        exs.filter { it.depth() < MAX_DEPTH } to applyOrError(currTy, t)
                    }.filterKeys { it.isNotEmpty() }.entries.partition { it.value !is Err }
                    val tmp = mutableListOf<Pair<Type, Example>>()
                    goodArgs.map { it.key to (it.value as Ok).result }.forEach { (args, typeAfterArg) ->
                        args.forEach {
                            val ex = App(currEx, it)
                            tmp.add(typeAfterArg to ex)
                            // TODO there is a more efficient way probably since there are multiple examples with same fn type
                            if (typeAfterArg is Function)
                                inProgress.add(ex to typeAfterArg)
                        }
                    }
                    tmp.forEach {  // I think this avoids concurrentmodificationexcedption
                        addPos(it.first, it.second)
                    }

                    badArgs.flatMap { it.key.map { k -> k to it.value as Err } }
                        .forEach { (ex, err) -> addNeg(err.error, App(currEx, ex)) }
                }
            }
            // TODO we can purposefully add some negative examples where we apply too many arguments, although
            //  it shouldn't be necessary}
        }
        fnDummies.forEach { (n, t) -> addPos(t, Name(n)) }

        println(negExamples.entries.map { "${it.key}\t${it.value.size}" })

        return Pair(Query(posExamples.values.flatten(), negExamples.values.flatten(), includesSubexprs = true), dummies)
        // TODO Want minimal negexs. Also, instead of keeping all, we could discard if we have >5 for that error type for that fn name already! actually we want >5 of them for that parameter of that fn. if fn has 5 params we want few examples of each being wrong
    }
}

fun main() {
//    val groundTruth = listOf("(i)", "(b)", "(-> a (-> (l a) (l a)))")
    val groundTruth = listOf(
        "(i)", "(b)",
        "(d (i) (b))",
        "(d (b) (i))",
        "(d (i) (i))",
        "(d (b) (b))",
        "(-> (d k v) (-> k (-> v (d k v))))"
    )

    val (query, context) = ExampleGenerator(2,
        2,
        200,
        groundTruth.map { SExprParser(it).parse().toType() to null }).examples()
    println(context.toList().joinToString(separator = "\n"))
    println("Positive examples:")
    println(query.posExamples.size)
    println(printInvertDummies(query.posExamples.map { it.flatten() }, context))
    println(query.negExamples.size)
}

fun printInvertDummies(exs: Collection<FlatApp>, context: Assignment): String {
    fun replaceDummiesWithTypeString(app: FlatApp): FlatApp =
        FlatApp(if (app.args.isEmpty()) "${context[app.name]}" else "(${context[app.name]}). ",
            app.args.map { replaceDummiesWithTypeString(it) })
    return exs.map { replaceDummiesWithTypeString(it) }.joinToString(separator = "\n")
}
