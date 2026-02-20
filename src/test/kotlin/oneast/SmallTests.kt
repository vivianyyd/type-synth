package oneast

import fixtures.data.DictTest
import query.Example
import util.Logger
import util.io.parseTest
import kotlin.test.Test

class SmallTests {
    private fun defaultLogger(config: Configuration) =
        Logger(configuration = config, logFilename = "tmp.log", logToFile = true, verbosity = 5)

    private fun defaultConfig(name: String) =
        Configuration(
            name = name,
            runCVC = true,
            sizeBound = 20,
            depthBound = 4,
            namesPerRound = 10,
            numSols = Solutions.NumSolutions(1)
        )

    @Test
    fun `recovers dict chain types`() {
        val testName = "dictchain"
        val query = parseTest(testName)
        val languageGroundTruth: (Example) -> Boolean = { e -> TODO() }

        val configuration = defaultConfig(testName)
        val logger = defaultLogger(configuration)

        assert(run(query, languageGroundTruth, configuration, logger).isNotEmpty())
    }

    @Test
    fun `recovers dict put types`() {
        val query = DictTest
        val languageGroundTruth: (Example) -> Boolean = { e -> TODO() }

        val configuration = defaultConfig("Dict Put")
        val logger = defaultLogger(configuration)

        assert(run(query, languageGroundTruth, configuration, logger).isNotEmpty())
    }
}
