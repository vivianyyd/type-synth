package core

import core.enumerate.EnumeratorTag
import core.enumerate.enumerator
import core.enumerate.solutions
import core.languages.*
import core.unification.UnificationTag
import core.unification.unification
import query.App
import query.Name
import util.Configuration
import util.Logger
import util.io.cvc.clearCVC
import util.io.parseTest
import util.lazyCartesianProduct
import util.time

fun main() {
    val testFromFile = parseTest("dictchain")

    val configuration =
        Configuration(
            querySpec = testFromFile,
            runCVC = true,
            enumeratorTag = EnumeratorTag.DFSPriority,
            unificationTag = UnificationTag.Eager,
            finalRoundSketches = true,
            sizeBound = 20,
            depthBound = 4
        )

    val logger =
        Logger(
            configuration = configuration, logFilename = "tmp.log", logToFile = true, verbosity = 5
        )

    run(configuration, logger)
}

fun run(configuration: Configuration, logger: Logger) {
    if (configuration.runCVC) clearCVC()
    val (query, oracle) = configuration.querySpec.pair()

    fun <L : Language> makeEnumerator(seed: Candidate<L>, mustPassNegatives: Boolean) =
        enumerator(
            configuration.enumeratorTag,
            query,
            seed,
            unification(configuration.unificationTag),
            mustPassNegatives,
            logger
        )

    val initSeed =
        Candidate(
            query.names,
            query.names.map { name ->
                if (query.posWithSubexprs.any { it is App && it.fn is Name && it.fn.name == name })
                    InitHole().fnExpansion
                else InitL
            })
    val initSols =
        logger.time("Init search") {
            solutions(
                listOf(makeEnumerator(initSeed, false)),
                false,
                configuration.sizeBound,
                configuration.depthBound,
                fastForward = false,
                iterative = false,
                logger
            )
        }

    val elabSeeds = logger.time("Compile Init to Elab") { initSols.map { compileInit(it) } }
    val elabSols =
        logger.time("Elab search") {
            solutions(
                elabSeeds.map { makeEnumerator(it, false) },
                false,
                configuration.sizeBound,
                configuration.depthBound,
                iterative = false,
                fastForward = false,
                logger = logger
            )
        }

    Hole.resetIds() // quality of life

    val concSeeds =
        logger.time("Compile Elab to Concrete") {
            elabSols
                .mapNotNull {
                    compileElabToInfo(
                        it,
                        query,
                        oracle,
                        unification(configuration.unificationTag),
                        configuration.runCVC
                    )
                }
                .flatMap { info ->
                    lazyCartesianProduct(info.labelArities.values.map { (0..it).toList() }).map {
                        info.copy(labelArities = info.labelArities.keys.zip(it).toMap())
                    }
                } // TODO reorder these simplest to most complex
                .map { compileToConcrete(it, emitBlanks = false) }
        }
    logger.log("Concrete seeds: ${concSeeds.size}\n${concSeeds.joinToString(separator = "\n")}")

    val concSols =
        logger.time("Concrete search") {
            solutions(
                concSeeds.map { makeEnumerator(it, true) },
                configuration.finalRoundSketches,
                configuration.sizeBound,
                configuration.depthBound,
                iterative = true,
                fastForward = configuration.finalRoundSketches,
                logger = logger
            )
        }

    logger.log("FINAL SOLUTIONS:")
    logger.log(concSols.joinToString(separator = "\n"))

    logger.finish()
}
