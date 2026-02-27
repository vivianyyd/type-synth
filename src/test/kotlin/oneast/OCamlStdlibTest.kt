package oneast

import oneast.searchstrategies.DFSEnumerator
import testutil.loadQuery
import testutil.ocaml.OCamlChecker
import testutil.ocaml.OcamlTypeParser
import util.Logger
import util.NewCheckingOracle
import util.io.cvc.clearCVC
import util.join
import java.io.File
import kotlin.test.Test

class OCamlStdlibTest {
    @Test
    fun `can reconstruct stdlib`() {
        val dir = join("src", "test", "input", "ocaml-stdlib")
        val query = loadQuery(File(dir))
        val oracleTypes = OcamlTypeParser().parseSignatures(File(join(dir, "all.types")).readText())
        val oracle = NewCheckingOracle(oracleTypes)

        val configuration =
            Configuration(
                name = "OCaml Stdlib",
                runCVC = true,
                sizeBound = 20,
                depthBound = 4,
                namesPerRound = 5,
                numSols = Solutions.NumSolutions(1)
            )

        val logger =
            Logger(
                configuration = configuration,
                logFilename = "tmp.log",
                logToFile = true,
                verbosity = 5
            )

        clearCVC() // TODO This should really be done by the engine or someone else
        val engine =
            Engine(
                query,
                { s, q ->
                    logger.log("Searching $s")
                    Search(s, q, oracle, configuration, ::DFSEnumerator, logger)
                },
                { e -> OCamlChecker().isValid(e.toString()).isValid },
                logger,
                namesPerRound = configuration.namesPerRound
            )
        // TODO oracle should be in query, numsols in config

        engine.search().take(1).forEach { logger.log("FIRST SOLUTION: ${it.asMap()}") }
        logger.finish()
    }
}
