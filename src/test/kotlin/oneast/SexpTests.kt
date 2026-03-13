package oneast

import oneast.searchstrategies.DFSEnumerator
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource
import util.GroundTruth
import util.Logger
import util.io.parseTest
import kotlin.test.Test

class SexpTests {
    companion object {
        @JvmStatic
        fun testNames() =
            listOf(
                "cons",
                "dictchain",
                "dictput",
                "hofs",
                "id-inc",
                "polymorphic-dictchain",
                "polymorphic-nil",
            )
    }

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

    @ParameterizedTest
    @MethodSource("testNames")
    fun `validate tests`(name: String) {
        val query = parseTest(name)
        query.examples.posNoSubexprs.forEach {
            assert(query.oracle.valid(it)) { "Bad positive example: $it" }
        }
        query.examples.neg.forEach {
            assert(!query.oracle.valid(it)) { "Bad negative example: $it" }
        }
    }

    @ParameterizedTest
    @MethodSource("testNames")
    fun test(testName: String) {
        val query = parseTest(testName)
        val languageGroundTruth: GroundTruth = query.oracle
        val configuration = defaultConfig(testName)
        val logger = defaultLogger(configuration, logName = testName)

        assert(run(query, languageGroundTruth, configuration, logger).isNotEmpty())
    }

    @Test
    fun `recovers dict chain types`() = test("dictchain")

    @Test
    fun `recovers cons types`() = test("cons")

    @Test
    fun `polymorphic dict chain`() = test("polymorphic-dictchain")
}
