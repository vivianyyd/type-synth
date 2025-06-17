import constraints.LabelConstraintGenerator
import dependencyanalysis.DependencyAnalysis
import query.parseContextAndExamples
import sta.SymTypeABuilder
import stc.SymTypeCEnumerator
import stc.toSExpr
import test.ConsTest
import test.DictTest
import test.HOFTest
import test.IdTest
import util.*

const val ROUNDS = 4
const val MAKE_OUTLINES = true
const val CALL_CVC = true

fun main() {
    val idtest = IdTest
    val constest = ConsTest
    val hoftest = HOFTest
    val dicttest = DictTest
    val test = dicttest
//    val (query, oracle) = (test.query to test.oracle)

    val (query, oracle) = parseContextAndExamples(readExamples("dictchain"))

    val projections =
        if (MAKE_OUTLINES) SymTypeCEnumerator(query, SymTypeABuilder(query).make, oracle).enumerateAll()
        else readIntermediateOutlines()
    if (MAKE_OUTLINES) projections.forEachIndexed { i, it ->
        writeIntermediateOutline("${it.outline.toSExpr()}", "$i")
    }

    // No need for dep analysis for every candidate, just every arrow skeleton (unique mappings of name to num params)
    val deps = projections.map { it.arities }.toSet().associateWith { DependencyAnalysis(query, it, oracle) }
    val constrGenerators = projections.associateWith { LabelConstraintGenerator(it, deps[it.arities]!!) }
    projections.forEachIndexed { i, it ->
        if (CALL_CVC) {
            callCVC(constrGenerators[it]!!.gen(), "$i")
        }
    }

    readCVCresults().forEach { (testName, s) ->
        val i = testName.toInt()
        println(projections[i].outline)
        CVCParser(s, constrGenerators[projections[i]]!!).print()
        TODO("Request a smaller answer from CVC")

    }

    TODO("Use CVC output for enumeration")
    TODO("Can names be observationally equal wrt where they're used but not actually due to differences in arguments they expect? It doesn't break our blind unionfind labels for values that are obs equiv, but maybe it breaks other stuff esp when we have HOFs... Actually I think it's fine bc the way we do observational equiv is we substitute one for the other for ALL occurrences including as the function in an application. That's really expensive to do with examples though)")
    TODO("When doing final enumeration, take step in each candidate")

//    val concEnum = ConcreteEnumerator(
//        query,
//        candidate,
//        mapOf(0 to 0, 2 to 1),  // TODO call label solver
//        depAnalysis,
//        oracle
//    )
//    concEnum.callMe(2)
//    val contexts = concEnum.contexts().filter { concEnum.check(it) }
//    contexts.forEach { println(it.toList().joinToString(separator = "\n", postfix = "\n---\n")) }
//    println(contexts.size)
//    val gener = constraints.LabelConstraintGenerator(depAnalysis)
//    println(gener.gen())

}

fun <T> Iterable<T>.pr() = this.joinToString(separator = "\n")
