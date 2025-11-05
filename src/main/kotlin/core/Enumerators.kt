package core

import core.enumerate.DFSPriorityEnumerator
import query.App
import query.Name
import query.parseContextAndExamples
import test.*
import util.clearCVC
import util.lazyCartesianProduct
import util.readExamples
import java.io.File
import java.io.PrintStream

val RERUN_CVC = false

fun main() {
    if (RERUN_CVC) clearCVC()

    val logFile = File("app.log")
    val logStream = PrintStream(logFile.outputStream(), true)
//    System.setOut(logStream)
//    System.setErr(logStream)

    val smallTests = listOf(IdTest, ConsTest, HOFTest, DictTest, WeirdTest)
    val t = DictTest
    val testFromFile = parseContextAndExamples(readExamples("dictchain"))

    val (query, oracle) = t.query to t.oracle
//    val (query, oracle) = testFromFile

    // TODO set unification algo once up here, it just gets referenced below


    val inits = lazyCartesianProduct(
        query.names.map { name ->
            InitHole().expansions(Empty(), setOf(), null).map { it.first }
                .filter { it is InitL || (it is NArrow && query.posExamples.any { it is App && it.fn is Name && it.fn.name == name }) }
        }).map { Candidate(query.names, it) }

    fun <L : Language> enum(seed: Candidate<L>, maxDepth: Int): List<Candidate<L>> =
        DFSPriorityEnumerator(query, seed, ::EagerUnification, false).enumerate(maxDepth)

    fun <L : Language> fromSeeds(seeds: Sequence<Candidate<L>>, maxDepth: Int): Sequence<Candidate<L>> =
        seeds.flatMap { enum(it, maxDepth) }

    val TIME = System.currentTimeMillis()

    val initSols = fromSeeds(inits, 4)
    var elabSols = fromSeeds(initSols.map { compileInit(it) }, 4)

    val concEnumerators = elabSols.mapNotNull {
        compileElab(it, query, oracle, ::EagerUnification, RERUN_CVC)?.let {
            DFSPriorityEnumerator(query, it, ::EagerUnification, mustPassNegatives = true, minimizeSize = true)
        }
    }.toList() // This needs to be a list so we don't keep calling it...

    println(concEnumerators.joinToString(separator = "\n") { "${it.seedCandidate}" })

    val sol = mutableListOf<Candidate<Concrete>>()
    for (i in 1..4) {
        println("Hello $i")
        val sols = concEnumerators.flatMap { it.enumerate(i) }.toList()
        if (sols.isNotEmpty()) {
            sol.addAll(sols)
            break
        }
    }

    println("FINAL SOLUTIONS:")
    println(sol.joinToString(separator = "\n"))

    println("TIME: ${System.currentTimeMillis() - TIME}")

    TODO("BRING BACK CEGIS LOOP")
//    println(solslist.joinToString(prefix = "SOLUTIONS:\n", separator = "\n"))
    TODO("Stop enumerating if we have all solutions of min size")
    TODO("Canonicalize wrt alpha equiv before storing in seen?")
    TODO(
        "In the next step, should we allow new labels to be introduced in expansions? " + "Will there ever be problems where a label type only occurs within other label types as a param?"
    )
}
