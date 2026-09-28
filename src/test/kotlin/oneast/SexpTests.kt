package oneast

import bench.Debug
import org.junit.jupiter.api.Test
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource
import testutil.loadQueryFromFile

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

        val defaultConfig =
            Configuration(
                sizeBound = 20,
                depthBound = 4,
                scheduleInfo = SingleRound,
                numSols = Solutions.NumSolutions(1)
            )
    }

    @Test
    fun `just one`() {
        Debug.enabled = true
        try {
            test("cons")
        } finally {
            Debug.enabled = false
        }
    }

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
    fun test(testName: String) {
        val query = loadQueryFromFile(testName)
        assert(run(query, query.oracle, defaultConfig).isNotEmpty())
    }
}
