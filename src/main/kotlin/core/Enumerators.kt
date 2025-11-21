package core

import core.enumerate.EnumeratorTag
import core.enumerate.enumerator
import core.enumerate.solutions
import query.App
import query.Name
import query.parseTest
import test.*
import util.Configuration
import util.Logger
import util.clearCVC

fun main() {
    val tests = listOf(IdTest, ConsTest, HOFTest, DictTest, WeirdTest)
    val testFromFile = parseTest("dictchain")

    val configuration = Configuration(
        test = testFromFile,
        runCVC = true,
        enumeratorTag = EnumeratorTag.DFSPriority,
        unificationTag = UnificationTag.Eager,
        finalRoundSketches = false,
        sizeBound = 20,
        depthBound = 4
    )

    val logger = Logger(
        configuration = configuration,
        logFilename = "dictchain-ff.log",
        logToFile = true,
        verbosity = 5
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

    fun <T> time(name: String, block: () -> T): T {
        logger.start(name)
        val result = block()
        logger.stop(name)
        return result
    }

    val initSeed = Candidate(
        query.names,
        query.names.map { name ->
            if (query.posExamples.any { it is App && it.fn is Name && it.fn.name == name })
                InitHole().fnExpansion
            else InitL
        })
    val initSols = time("Init search") {
        solutions(
            listOf(makeEnumerator(initSeed, false)),
            configuration.sizeBound,
            configuration.depthBound,
            skipSizeIfCantFillAll = true,
            iterative = false,
            logger
        )
    }

    val elabSeeds = time("Compile Init to Elab") { initSols.map { compileInit(it) } }
    val elabSols = time("Elab search") {
        solutions(
            elabSeeds.map { makeEnumerator(it, false) },
            configuration.sizeBound,
            configuration.depthBound,
            iterative = false,
            skipSizeIfCantFillAll = true,
            logger = logger
        )
    }

    Hole.resetIds() // quality of life

    val concSeeds = time("Compile Elab to Concrete") {
        elabSols.mapNotNull {
            compileElab(
                it,
                query,
                oracle,
                unification(configuration.unificationTag),
                configuration.runCVC
            )
        }
    }
    println(concSeeds.joinToString(separator = "\n"))

    val concSols = time("Concrete search") {
        solutions(
            concSeeds.map { makeEnumerator(it, true) },
            configuration.sizeBound,
            configuration.depthBound,
            iterative = true,
            skipSizeIfCantFillAll = !configuration.finalRoundSketches,
            logger = logger
        )
    }

    println("FINAL SOLUTIONS:")
    println(concSols.joinToString(separator = "\n"))

    logger.finish()
}
