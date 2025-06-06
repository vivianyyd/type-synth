import symbolicgen.DependencyAnalysis
import symbolicgen.concreteenumerator.ConcreteEnumerator
import symbolicgen.sta.SymTypeABuilder
import symbolicgen.stc.SymTypeCEnumerator
import symbolicgen.std.flatten
import test.ConsTest
import test.HOFTest
import test.IdTest

const val ROUNDS = 4
const val RUN_SKETCH = true

fun main() {
    val idtest = IdTest
    val constest = ConsTest
    val hoftest = HOFTest
    val test = constest

    val (query, oracle) = (test.query to test.oracle)
    val b = SymTypeABuilder(query).make
//    b.printState()

    val enum = SymTypeCEnumerator(query, b, oracle)
    val specializedSymbolicTypes = enum.enumerateAll()
//    println(specializedSymbolicTypes.pr())

    val candidate = specializedSymbolicTypes[7]
    println(candidate)

    val depAnalysis = DependencyAnalysis(query, candidate, oracle)

    val concEnum = ConcreteEnumerator(
        query,
        candidate.mapValues { it.value.flatten() },
        mapOf(0 to 0, 2 to 1),  // TODO call label solver
        depAnalysis,
        oracle
    )
    concEnum.callMe(2)
    val contexts = concEnum.contexts().filter { concEnum.check(it) }
    contexts.forEach { println(it.toList().joinToString(separator = "\n", postfix = "\n---\n")) }
    println(contexts.size)
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
