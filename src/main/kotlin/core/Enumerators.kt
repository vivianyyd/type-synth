package core

import core.enumerate.EnumeratorTag
import core.enumerate.enumerator
import query.App
import query.Name
import query.parseTest
import test.*
import util.Configuration
import util.Logger
import util.clearCVC
import util.lazyCartesianProduct

fun main() {
    val tests = listOf(IdTest, ConsTest, HOFTest, DictTest, WeirdTest)
    val testFromFile = parseTest("dictchain")

    val configuration = Configuration(
        test = ConsTest,
        runCVC = true,
        enumeratorTag = EnumeratorTag.DFSPriority,
        unificationTag = UnificationTag.Eager,
        maxDepth = 4
    )

    val logger = Logger(
        configuration = configuration,
        logToFile = false
    )

    run(configuration, logger)
}

fun run(configuration: Configuration, logger: Logger) {
    if (configuration.runCVC) clearCVC()
    val (query, oracle) = configuration.test.pair()

    fun <L : Language> makeEnumerator(seed: Candidate<L>, mustPassNegatives: Boolean) =
        enumerator(
            configuration.enumeratorTag,
            query,
            seed,
            unification(configuration.unificationTag),
            mustPassNegatives,
            logger
        )

    val initSeeds = lazyCartesianProduct(
        query.names.map { name ->
            InitHole()
                .expansions(Empty(), setOf(), null)
                .map { it.first }
                .filter { it is InitL || (it is NArrow && query.posExamples.any { it is App && it.fn is Name && it.fn.name == name }) }
        }).map { Candidate(query.names, it) }
    val initSols = initSeeds.flatMap { makeEnumerator(it, false).enumerate(configuration.maxDepth) }

    val elabSeeds = initSols.map { compileInit(it) }
    val elabSols = elabSeeds.flatMap { makeEnumerator(it, false).enumerate(configuration.maxDepth) }

    val concSeeds = elabSols.mapNotNull {
        compileElab(
            it,
            query,
            oracle,
            unification(configuration.unificationTag),
            configuration.runCVC
        )
    }.toList()  // This needs to be a list so we don't keep calling it
    println(concSeeds.joinToString(separator = "\n"))
    val concEnumerators = concSeeds.map { makeEnumerator(it, true) }
    val concSols = mutableListOf<Candidate<Concrete>>()
    for (i in 1..configuration.maxDepth) {
        println("Hello $i")
        val sols = concEnumerators.flatMap { it.enumerate(i) }.toList()
        if (sols.isNotEmpty()) {
            concSols.addAll(sols)
            break
        }
    }

    println("FINAL SOLUTIONS:")
    println(concSols.joinToString(separator = "\n"))
}
