package oneast

import test.ConsTest
import test.Test
import util.Config
import util.Logger

val configuration =
    Configuration(
        test = ConsTest, runCVC = true, sizeBound = 20, depthBound = 4, namesPerRound = 10
    )

val logger =
    Logger(configuration = configuration, logFilename = "tmp.log", logToFile = true, verbosity = 5)

fun main() {
    val h = ConsTest // SomeHaskell

    val start = System.currentTimeMillis()

    val scheduler = Scheduler(h.query, h.oracle, namesPerRound = configuration.namesPerRound)

    scheduler
        .queries { nextQuery, nextSeed ->
            EnumerateOneAST(
                seed = nextSeed,
                query = nextQuery,
                oracle = h.oracle,
                hardSizeBound = 20,
                hardDepthBound = 4,
                logger = logger,
            )
                .enumerate(callSolver = true, numSols = Solutions.ONE_SOLUTION)
                .first()
            //            val sols = mutableListOf<SearchState>()
            //            for (depth in 2..configuration.depthBound) {
            //                logger.start("Depth $depth")
            //                for (size in 1..configuration.sizeBound) {
            //                    logger.start("Size $size")
            //
            //                    val currSols =
            //                        listOf(
            //                            EnumerateOneAST(
            //                                seed = nextSeed,
            //                                query = nextQuery,
            //                                oracle = h.oracle,
            //                                hardSizeBound = 20,
            //                                hardDepthBound = 4,
            //                                logger = logger,
            //                            )
            //                                .enumerate(callSolver = true, numSols =
            // Solutions.ONE_SOLUTION)
            //                                .first()
            //                        )
            //
            //                    logger.stop("Size $size")
            //                    if (currSols.isNotEmpty()) {
            //                        sols.addAll(currSols)
            //                        logger.log("STOPPED AT SIZE $size")
            //                        break
            //                    }
            //                }
            //                logger.stop("Depth $depth")
            //                if (sols.isNotEmpty()) {
            //                    logger.log("STOPPED AT DEPTH $depth")
            //                    break
            //                }
            //            }
            //            sols.first()
        }
        .forEach { if (it is Step.StateReady) println(it.state.asMap()) }
    println("${System.currentTimeMillis() - start} ms")
    TODO(
        "We can't just take the first result, need to do all of them. Large search tree wraps small search tree" +
                "Also we should use conservative fast forward every once in a while or every time idk"
    )
}

// TODO this is kind of a dummy config, only gets used for logging

data class Configuration(
    val test: Test,
    val runCVC: Boolean,
    val sizeBound: Int,
    val depthBound: Int,
    val namesPerRound: Int
) : Config {
    override fun toString(): String =
        listOf(
            test.name,
            "Running CVC: $runCVC",
            "Size bound: $sizeBound",
            "Depth bound: $depthBound",
            "Names per round: $namesPerRound"
        )
            .joinToString(separator = "\n", postfix = "\n=====\n")
}
