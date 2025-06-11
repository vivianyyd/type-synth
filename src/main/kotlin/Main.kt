import symbolicgen.DependencyAnalysis
import symbolicgen.LabelConstraintGenerator
import symbolicgen.sta.SymTypeABuilder
import symbolicgen.stc.*
import test.ConsTest
import test.DictTest
import test.HOFTest
import test.IdTest
import util.callCVC
import util.parse
import util.readCVCresults

const val ROUNDS = 4
const val RUN_SKETCH = true

fun main() {
    val idtest = IdTest
    val constest = ConsTest
    val hoftest = HOFTest
    val dicttest = DictTest
    val test = dicttest

    val (query, oracle) = (test.query to test.oracle)
    val b = SymTypeABuilder(query).make
    b.printState()

    val projections = SymTypeCEnumerator(query, b, oracle).enumerateAll()
//    println(projections.pr())

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

    val callcvc = false
    if (callcvc) {
        projections.forEachIndexed { i, it ->
            callCVC(LabelConstraintGenerator(it, deps[skeletonSizes[it]!!]!!).gen(), "$i")
        }
        projections.forEachIndexed { i, it ->
            if (i in listOf(41, 44, 48, 50)) println(it)
        }
    }

    // TODO pretty thrilling how many candidates get pruned away simply from being unsatisfiable!!!!!!!
    readCVCresults().forEach {
        println(parse(it).joinToString(separator = "\n"))
        println()
        println()

    }


    TODO("Call cvc to solve label constraints, parse them, then use them for enumeration")

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
