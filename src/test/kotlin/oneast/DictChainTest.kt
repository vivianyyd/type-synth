package oneast

import oneast.searchstrategies.DFSEnumerator
import util.Logger
import util.io.parseTest
import kotlin.test.Test

class DictChainTest {
    @Test
    fun `can build query from input file`() {
        val query = parseTest("dictchain")

        val configuration =
            Configuration(
                name = "dictchain",
                runCVC = true,
                sizeBound = 20,
                depthBound = 4,
                namesPerRound = 10,
                numSols = Solutions.NumSolutions(1)
            )

        val logger =
            Logger(
                configuration = configuration,
                logFilename = "tmp.log",
                logToFile = true,
                verbosity = 5
            )

        val engine =
            Engine(
                query.examples,
                { s, q ->
                    logger.log("Searching $s")
                    Search(s, q, query.oracle, configuration, ::DFSEnumerator, logger)
                },
                { e -> TODO() },
                logger,
                namesPerRound = configuration.namesPerRound
            )

        engine.search().take(1).forEach { logger.log("FIRST SOLUTION: ${it.asMap()}") }
        logger.finish()
    }
}
