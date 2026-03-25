package oneast

import oneast.searchstrategies.DFSEnumerator
import org.junit.jupiter.api.Disabled
import org.junit.jupiter.api.Test
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource
import util.GroundTruth
import util.Logger
import util.io.parseTest
import util.lines

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
            scheduleInfo = Auto(5),
            numSols = Solutions.NumSolutions(1)
        )

    @Disabled
    @Test
    fun `just one`() = test("hofs")

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

    @Test
    fun main() {
        val query = parseTest("option")

        // This gets killed at dependency analysis: Why?
        // Num=L0[], Str=L1[], cons=V0 -> L2[] -> L2[], fst=L3[] -> V0, nil=L2[], pair=V0 -> V1 ->
        // L3[], snd=L3[] -> V0, true=L4[]}

        //        val map =
        //            mapOf(
        //                "Num" to NamedLabel(0, emptyList()),
        //                "Str" to NamedLabel(1, emptyList()),
        //                "true" to NamedLabel(3, emptyList()),
        //                "pair" to
        //                        Arrow(
        //                            Variable(0),
        //                            Arrow(Variable(1), NamedLabel(2, listOf(Variable(0),
        // Variable(1))))
        //                        ),
        //                "fst" to Arrow(NamedLabel(2, listOf(Variable(0), Variable(1))),
        // Variable(0)),
        //                "snd" to Arrow(NamedLabel(2, listOf(Variable(0), Variable(1))),
        // Variable(1)),
        //                "cons" to
        //                        Arrow(
        //                            Variable(0),
        //                            Arrow(
        //                                NamedLabel(4, listOf(Variable(0))),
        //                                NamedLabel(4, listOf(Variable(0)))
        //                            )
        //                        ),
        //                "nil" to NamedLabel(4, listOf(Variable(0))),
        //            )
        //        val tmpor = CheckingGroundTruthOracle(map)
        //        query.examples.posNoSubexprs.forEach {
        //            if (it.names.all { it in map } && !tmpor.valid(it)) println("Failed posex
        // $it")
        //        }
        //        query.examples.neg.forEach {
        //            if (it.names.all { it in map } && tmpor.valid(it)) println("Failed negex $it")
        //        }

        val (pos, neg) = query.examples.posNoSubexprs.partition { query.oracle.valid(it) }

        println("POS:")
        println(pos.map { "(+ ($it))" }.lines())
        println("NEG:")
        println(neg.map { "(- ($it))" }.lines())
    }

    @ParameterizedTest
    @MethodSource("testNames")
    fun test(testName: String) {
        val query = parseTest(testName)
        val languageGroundTruth: GroundTruth = query.oracle
        val configuration = defaultConfig(testName)
        val logger = defaultLogger(configuration)

        assert(run(query, languageGroundTruth, configuration, logger).isNotEmpty())
    }
}
