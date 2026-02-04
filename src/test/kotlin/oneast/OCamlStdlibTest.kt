package oneast

import fixtures.OcamlTypeParser
import fixtures.loadQuery
import oneast.searchstrategies.DFSEnumerator
import util.Logger
import util.NewCheckingOracle
import util.io.parseTest
import util.join
import java.io.File
import kotlin.test.Test

class OCamlStdlibTest {
    @Test
    fun `can build query from input file`() {
        val dir = join("src", "test", "input", "ocaml-stdlib")
        val query = loadQuery(File(dir))
        val oracleTypes = OcamlTypeParser().parseSignatures(File(join(dir, "all.types")).readText())
        val oracle = NewCheckingOracle(oracleTypes)

        val configuration =
            Configuration(
                querySpec = parseTest("dictchain"),
                runCVC = true,
                sizeBound = 20,
                depthBound = 4,
                namesPerRound = 5
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
                query,
                { q, s ->
                    println(s)
                    Search(s, q, oracle, configuration, ::DFSEnumerator, logger)
                },
                namesPerRound = configuration.namesPerRound
            )
        // TODO oracle should be in query, numsols in config

        engine.search().take(1).forEach { logger.log("FIRST SOLUTION: ${it.asMap()}") }
        logger.finish()
    }
}
