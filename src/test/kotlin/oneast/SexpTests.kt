package oneast

import oneast.searchstrategies.DFSEnumerator
import org.junit.jupiter.api.Test
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource
import testutil.loadQueryFromFile
import util.GroundTruth
import util.Logger

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
            configuration = config,
            logFilename = "$logName-willBeOverwritten.log",
            logToFile = true,
            verbosity = 5
        )

    private fun defaultConfig(name: String) =
        Configuration(
            name = name,
            searchStrategy = ::DFSEnumerator,
            sizeBound = 20,
            depthBound = 4,
            scheduleInfo = SingleRound,
            numSols = Solutions.NumSolutions(1)
        )

    @Test
//    @Disabled
    fun `just one`() = test("polymorphic-dictchain")

    @ParameterizedTest
    @MethodSource("testNames")
    fun `validate tests`(name: String) {
        val query = loadQueryFromFile(name)
        query.examples.posNoSubexprs.forEach {
            assert(query.oracle.valid(it)) { "Bad positive example: $it" }
        }
        query.examples.neg.forEach {
            assert(!query.oracle.valid(it)) { "Bad negative example: $it" }
        }
    }

    @ParameterizedTest
    @MethodSource("testNames")
//    @Disabled
    fun test(testName: String) {
        val query = loadQueryFromFile(testName)
        val languageGroundTruth: GroundTruth = query.oracle
        val configuration = defaultConfig(testName)
        val logger = defaultLogger(configuration)

        assert(run(query, languageGroundTruth, configuration, logger).isNotEmpty())
    }
}
