import concreteenumerator.ConcreteEnumerator
import concreteenumerator.Node
import constraints.LabelConstraintGenerator
import dependencyanalysis.DependencyAnalysis
import query.parseContextAndExamples
import sta.SymTypeABuilder
import stc.SymTypeCEnumerator
import stc.toSExpr
import util.*

const val ROUNDS = 4
const val WRITE_INTERMEDIATE = false
const val MAKE_OUTLINES = false
const val CALL_INIT_CVC = false
const val CALL_SMALLER_CVC = false

fun main() {
//    val idtest = IdTest
//    val constest = ConsTest
//    val hoftest = HOFTest
//    val dicttest = DictTest
//    val test = dicttest

    val examplesFromFile = parseContextAndExamples(readExamples("dictchain"))

//    val (query, oracle) = (test.query to test.oracle)
    val (query, oracle) = examplesFromFile
    if (MAKE_OUTLINES) clearOutlines()
    if (CALL_INIT_CVC || CALL_SMALLER_CVC) clearCVC()

    val TIME = System.currentTimeMillis()

    val projections =
        if (MAKE_OUTLINES) SymTypeCEnumerator(query, SymTypeABuilder(query).make, oracle).enumerateAll()
        else readIntermediateOutlines().map { it.second }
    if (MAKE_OUTLINES && WRITE_INTERMEDIATE) projections.forEachIndexed { i, it ->
        writeIntermediateOutline("${it.outline.toSExpr()}", "$i")
    }
    println(projections.joinToString(separator = "\n") { "${it.outline}" })

    println("Starting dep analysis")
    // No need for dep analysis for every candidate, just every arrow skeleton (unique mappings of name to num params)
    val deps = projections.map { it.arities }.toSet().associateWith { DependencyAnalysis(query, it, oracle) }
//    println(deps)
//    deps.entries.mapIndexed { i, it ->
//        viz("inc", it.value, "inc$i")
//        viz("id", it.value, "id$i")
//    }
    println("Calling CVC")
    val constrGenerators = projections.associateWith { LabelConstraintGenerator(it, deps[it.arities]!!) }
    projections.forEachIndexed { i, it ->
        if (CALL_INIT_CVC) {
            callCVC(constrGenerators[it]!!.initialQuery(), "$i")
        }
    }

    val OK = mutableListOf<Map<String, Node>>()

    readCVCresults().map { (name, contents) ->
        val i = name.toInt()
        val cvcGen = constrGenerators[projections[i]]!!
        var counter = 0
        var previousSolution = contents
        var lastSuccessful = -1
        do {
            println("Getting smaller CVC results")
            val parser = CVCParser(previousSolution, cvcGen)
            val testName = "$i-smaller${counter++}"
            val cont =
                if (/*CALL_SMALLER_CVC && */parser.sizes.isNotEmpty()) // TODO FIXME if the flag is off we don't read previous results properly
                    callCVC(cvcGen.smallerQuery(parser.sizes), testName)
                else false
            if (cont) {
                lastSuccessful = counter - 1
                previousSolution = readCVC(testName)
            }
        } while (cont)

        val finalSuccessfulOutput = if (lastSuccessful == -1) "$i" else "$i-smaller$lastSuccessful"
        val result = CVCParser(readCVC(finalSuccessfulOutput), cvcGen)
        result.print()
        val concEnum = ConcreteEnumerator(
            query,
            projections[i],
            result.sizes,
            deps[projections[i].arities]!!,
            oracle
        )
        println("Enumerating")
        val contexts = concEnum.callMe(2)
        OK.addAll(contexts)

    }

    OK.forEach {
        println(it.toList().joinToString(separator = "\n", postfix = "\n---\n"))
    }

    println("${OK.size} satisfying contexts")
    println("TIME: ${System.currentTimeMillis() - TIME}")

    TODO("Use dependency info for enumeration")
    // is it guaranteed that space of type assignments with only minimal satisfying label sizes contain the solution? YES, *IF* WE SEE ALL DATA CONSTRUCTORS
    TODO("Can names be observationally equal wrt where they're used but not actually due to differences in arguments they expect? It doesn't break our blind unionfind labels for values that are obs equiv, but maybe it breaks other stuff esp when we have HOFs... Actually I think it's fine bc the way we do observational equiv is we substitute one for the other for ALL occurrences including as the function in an application. That's really expensive to do with examples though)")
    TODO("When doing final enumeration, take step in each candidate")


//    val gener = constraints.LabelConstraintGenerator(depAnalysis)
//    println(gener.gen())

}

fun <T> Iterable<T>.pr() = this.joinToString(separator = "\n")
