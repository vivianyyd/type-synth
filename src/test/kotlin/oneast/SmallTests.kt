package oneast

import oneast.searchstrategies.DFSEnumerator
import util.GroundTruth
import util.Logger
import util.io.parseTest
import kotlin.test.Test
import kotlin.test.assertFalse
import kotlin.test.assertTrue

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

    private fun test(testName: String) {
        val query = parseTest(testName)
        val languageGroundTruth: GroundTruth = query.oracle
        val configuration = defaultConfig(testName)
        val logger = defaultLogger(configuration, logName = testName)

        assert(run(query, languageGroundTruth, configuration, logger).isNotEmpty())
    }

    @Test
    fun `validate tests`() {
        listOf("cons", "dictchain", "dictput", "hofs", "id-inc", "polymorphic-dictchain", "polymorphic-nil").forEach {
            val query = parseTest(it)
            query.examples.posNoSubexprs.forEach {
                assertTrue(query.oracle.valid(it), "Bad positive example: $it")
            }
            query.examples.neg.forEach {
                assertFalse(query.oracle.valid(it), "Bad negative example: $it")
            }
        }

    }

    @Test
    fun `recovers dict chain types`() = test("dictchain")

    @Test
    fun `recovers cons types`() = test("cons")

    @Test
    fun `polymorphic dict chain`() = test("polymorphic-dictchain")
}
