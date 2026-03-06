package oneast

import data.ConsTest
import data.DictTest
import oneast.searchstrategies.DFSEnumerator
import query.Example
import util.Logger
import util.io.parseTest
import kotlin.test.Test

class SmallTests {
    private fun defaultLogger(
        config: Configuration,
        logName: String = config.name.replace("[^A-Za-z0-9]".toRegex(), "-")
    ) =
        Logger(
            configuration = config, logFilename = "$logName.log", logToFile = true, verbosity = 5
        )

    private fun defaultConfig(name: String) =
        Configuration(
            name = name,
            searchStrategy = ::DFSEnumerator,
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
        val logger = defaultLogger(configuration, logName = "tmp")

        assert(run(query, languageGroundTruth, configuration, logger).isNotEmpty())
    }

    @Test
    fun `polymorphic dict chain`() {
        val testName = "polymorphic-dictchain"
        val query = parseTest(testName)
        val languageGroundTruth: (Example) -> Boolean = { e -> TODO() }

        val configuration = defaultConfig(testName)
        val logger = defaultLogger(configuration, logName = "tmp")

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

    @Test
    fun `recovers cons types`() {
        val query = ConsTest
        val languageGroundTruth: (Example) -> Boolean = { e -> TODO() }

        val configuration = defaultConfig("Cons")
        val logger = defaultLogger(configuration)

        assert(run(query, languageGroundTruth, configuration, logger).isNotEmpty())
    }
}
