import concreteenumerator.ConcreteEnumerator
import concreteenumerator.ConcreteNode
import constraints.LabelConstraintGenerator
import dependencyanalysis.DependencyAnalysis
import dependencyanalysis.viz
import query.Query
import query.parseContextAndExamples
import sta.SymTypeABuilder
import stc.*
import test.ConsTest
import test.DictTest
import test.HOFTest
import test.IdTest
import util.*

const val ROUNDS = 4
const val REDO_ALL = false
const val WRITE_INTERMEDIATE = REDO_ALL
const val MAKE_OUTLINES = REDO_ALL
const val CALL_INIT_CVC = REDO_ALL
const val CALL_SMALLER_CVC = REDO_ALL

fun main() {
    val smallTests = listOf(IdTest, ConsTest, HOFTest, DictTest)
    val smallTest = ConsTest
    val testFromFile = parseContextAndExamples(readExamples("toy"))

    val (query, oracle) = (smallTest.query to smallTest.oracle)
//    val (query, oracle) = testFromFile
//    viz(query)

    if (MAKE_OUTLINES) clearOutlines()
    if (CALL_INIT_CVC || CALL_SMALLER_CVC) clearCVC()
    val TIME = System.currentTimeMillis()

    val outlines = outlines(query, oracle)

    println("Starting dependency analysis")
    val aritiesToDeps = aritiesToDeps(query, oracle, outlines)
    vizDeps(listOf("cons"), aritiesToDeps)

    println("Searching for label sizes with CVC")
    val nodeSizes = assignLabelSizes(outlines, aritiesToDeps)

    println("Enumerating")
    val OK = mutableListOf<Map<String, ConcreteNode>>()
    nodeSizes.map { (i, labelSizes) ->
        println("\n\n")
        printSearchSeed(labelSizes, outlines[i])
        OK.addAll(
            ConcreteEnumerator(
                query,
                outlines[i],
                labelSizes,
                aritiesToDeps[outlines[i].arities]!!,
                oracle
            ).callMe(3)
        )
    }
    println("Solutions:")
    OK.forEach { println(it.toList().joinToString(separator = "\n", postfix = "\n---\n")) }
    println("${OK.size} satisfying contexts")
    println("TIME: ${System.currentTimeMillis() - TIME}")
}

private fun outlines(query: Query, oracle: EqualityNewOracle): List<Projection> {
    val projections = if (MAKE_OUTLINES) SymTypeCEnumerator(query, SymTypeABuilder(query).make, oracle).enumerateAll()
    else readIntermediateOutlines().map { it.second }
    if (MAKE_OUTLINES && WRITE_INTERMEDIATE) projections.forEachIndexed { i, it ->
        writeIntermediateOutline("${it.outline.toSExpr()}", "$i")
    }
    return projections
}

// No need for dep analysis for every candidate, just every arrow skeleton (unique mappings of name to arity)
private fun aritiesToDeps(
    query: Query,
    oracle: EqualityNewOracle,
    outlines: List<Projection>
): Map<Map<String, Int>, DependencyAnalysis> =
    outlines.map { it.arities }.toSet().associateWith { DependencyAnalysis(query, it, oracle) }

private fun vizDeps(components: List<String>, aritiesToDeps: Map<Map<String, Int>, DependencyAnalysis>) =
    aritiesToDeps.entries.mapIndexed { i, it -> components.map { f -> viz(f, it.value, "$f$i") } }

private fun assignLabelSizes(
    outlines: List<Projection>,
    aritiesToDeps: Map<Map<String, Int>, DependencyAnalysis>
): Map<Int, Map<L, Int>> {
    val cvcGens = outlines.withIndex()
        .associate { (i, outline) -> i to LabelConstraintGenerator(outline, aritiesToDeps[outline.arities]!!) }
    cvcGens.forEach { (i, gen) -> if (CALL_INIT_CVC) callCVC(gen.initialQuery(), "$i") }
    return readInitialCVCresults().associate { (i, contents) -> i to minLabelSizes(i, contents, cvcGens[i]!!) }
}

private fun minLabelSizes(testId: Int, prevSol: String, cvcGenerator: LabelConstraintGenerator): Map<L, Int> {
    var counter = 0
    var previousSolution = prevSol
    var lastSuccessful = -1
    do {
        println("Getting smaller CVC results")
        val parser = CVCParser(previousSolution, cvcGenerator)
        val testName = "$testId-smaller${counter++}"
        val cont =
            if (/*CALL_SMALLER_CVC && */parser.sizes.isNotEmpty()) // TODO FIXME if the flag is off we don't read previous results properly
                callCVC(cvcGenerator.smallerQuery(parser.sizes), testName)
            else false
        if (cont) {
            lastSuccessful = counter - 1
            previousSolution = readCVC(testName)
        }
    } while (cont)
    val finalSuccessfulOutput = if (lastSuccessful == -1) "$testId" else "$testId-smaller$lastSuccessful"
    return CVCParser(readCVC(finalSuccessfulOutput), cvcGenerator).sizes
}

private fun printSearchSeed(labelSizes: Map<L, Int>, outline: Projection) {
    fun SymTypeC.toStringWithSizes(): String = when (this) {
        is L -> "$this[${List(labelSizes[this]!!) { "_" }.joinToString(separator = ",")}]"
        is Var -> this.toString()
        is F -> "${if (left is F) "(${left.toStringWithSizes()})" else "${left.toStringWithSizes()}"} -> ${rite.toStringWithSizes()}"
    }
    println(
        outline.outline.entries.joinToString(
            prefix = "{",
            postfix = "}",
            separator = ", "
        ) { (component, type) -> "$component: ${type.toStringWithSizes()}" })

}

fun <T> Iterable<T>.pr() = this.joinToString(separator = "\n")
