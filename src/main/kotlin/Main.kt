import query.ExampleGenerator
import query.Query
import query.flatten
import query.printInvertDummies
import symbolicgen.DependencyAnalysis
import symbolicgen.DependencyVisualizer
import symbolicgen.LabelConstraintGenerator
import symbolicgen.sta.SymTypeABuilder
import symbolicgen.stc.*
import test.ConsTest
import test.DictTest
import test.HOFTest
import test.IdTest
import types.toType
import util.*

const val ROUNDS = 4
const val RUN_SKETCH = true

fun generate(types: List<String>): Pair<Query, CheckingOracle> {
    val (query, context) = ExampleGenerator(1,
        2,
        200,
        types.map { SExprParser(it).parse().toType() }).examples()
    println("Context:")
    println(context.toList().joinToString(separator = "\n"))
    println("Positive examples: ${query.posExamples.size}")
    println(printInvertDummies(query.posExamples.map { it.flatten() }, context))
    println("Negative examples: ${query.negExamples.size}")
    return query to CheckingOracle(context)
}

fun main() {
    // Handwritten tests
    val idtest = IdTest
    val constest = ConsTest
    val hoftest = HOFTest
    val dicttest = DictTest
    val test = dicttest

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

//    val (query, oracle) = (test.query to test.oracle)
    val (query, oracle) = (generate(dictchain))

    val b = SymTypeABuilder(query).make
    b.printState()
    println()

    val projections = SymTypeCEnumerator(query, b, oracle).enumerateAll()
    println(projections.pr())

    val skeletonSizes = projections.associateWith { proj ->
        proj.keys.associateWith {
            fun SymTypeC.params(): Int = when (this) {
                is F -> 1 + this.rite.params()
                is L, is Var -> 1
            }
            proj[it]!!.params()
        }
    }
    val sizeToCandidate = skeletonSizes.entries.associateBy({ it.value }) { it.key }
    // No need for dep analysis for every candidate, just every arrow skeleton (unique mappings of name to num params)
    val deps = skeletonSizes.values.associateWith { DependencyAnalysis(query, sizeToCandidate[it]!!, oracle) }
    deps.values.forEachIndexed { i, it ->
        DependencyVisualizer.viz(it.graphs["6"]!!, "put$i")
//        DependencyVisualizer.viz(it.graphs["7"]!!, "chain$i")
    }

    val constrGenerators = projections.associateWith { LabelConstraintGenerator(it, deps[skeletonSizes[it]!!]!!) }
    val write = false
    val callcvc = false
    println("Candidates: ${projections.size}")
    projections.forEachIndexed { i, it ->
        if (write) {
            callCVC(constrGenerators[it]!!.gen(), "$i", actuallyCall = callcvc)
        }
    }

    readCVCresults().zip(listOf(587, 629, 685, 713)).forEach { (s, i) ->
        println(projections[i])
        CVCParser(constrGenerators[projections[i]]!!).process(s)
        println()
        println()
    }

    TODO("example generation from types so that I can test chain.")
    TODO("What does cvc param varsets output look like for nonemtpy intersection, for example map chain?")
    TODO("Use CVC output for enumeration")
    TODO("Can names be observationally equal wrt where they're used but not actually due to differences in arguments they expect? It doesn't break our blind unionfind labels for values that are obs equiv, but maybe it breaks other stuff esp when we have HOFs... Actually I think it's fine bc the way we do observational equiv is we substitute one for the other for ALL occurrences including as the function in an application. That's really expensive to do with examples though)")
    TODO("When doing final enumeration, take step in each candidate")

//    val candidate = specializedSymbolicTypes[7]
//    println(candidate)
//
//    val concEnum = ConcreteEnumerator(
//        query,
//        candidate.mapValues { it.value.flatten() },
//        mapOf(0 to 0, 2 to 1),  // TODO call label solver
//        depAnalysis,
//        oracle
//    )
//    concEnum.callMe(2)
//    val contexts = concEnum.contexts().filter { concEnum.check(it) }
//    contexts.forEach { println(it.toList().joinToString(separator = "\n", postfix = "\n---\n")) }
//    println(contexts.size)
//    val gener = LabelConstraintGenerator(depAnalysis)
//    println(gener.gen())

//    specializedSymbolicTypes.forEachIndexed { i, context ->
//        query.names.forEach { name ->
//            DependencyGraphVisualizer.viz(DependencyAnalysis(query, context, oracle).graphs[name]!!, "$name-$i")
//        }
//    }
//
//    specializedSymbolicTypes.forEachIndexed { i, context ->
//        println(i)
//        println(context)
//        val sketcher = DepLabConcreteSketcher(
//            query,
//            context,
//            DependencyAnalysis(query, context, oracle),
//            enum.varTypeIds,
//            oracle
//        )
//        writeConcretizeInput(sketcher.query(), "test$i")
//    }

//    println(specializedSymbolicTypes)
//
//    b.deepen()
//    b.printState()
//    val enum2 = SymbolicEnumerator(query, b, oracle)
//    val specializedSymbolicTypes2 = enum.enumerateAll()
//    println(specializedSymbolicTypes2.size)

//    println(specializedSymbolicTypes.pr())
//    specializedSymbolicTypes.forEachIndexed { i, t ->
//        val sketcher = ConcreteSketcher(query, t, enum.varTypeIds, oracle)
//        writeConcretizeInput(sketcher.query(), "test$i")
//    }

//    val out = if (RUN_SKETCH) callSketch(sketcher.sketchInput(), "test") else readSketchOutput("test")
//    val (types, time) = (sketcher.parse(out))
//    println("${types.size} types in $time seconds")
}

fun <T> Iterable<T>.pr() = this.joinToString(separator = "\n")
