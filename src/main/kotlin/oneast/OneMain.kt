package oneast

import query.parseTest
import test.*
import util.Config
import util.Logger

val configuration =
    Configuration(
        test = ConsTest, runCVC = true, sizeBound = 20, depthBound = 4, namesPerRound = 10
    )

val logger =
    Logger(configuration = configuration, logFilename = "tmp.log", logToFile = true, verbosity = 5)

fun main() {
    val tests =
        listOf(IdTest, ConsTest, HOFTest, DictTest, WeirdTest, PolymorphicNil, PolymorphicDict)
    val testFromFile = parseTest("dictchain")

    val h = testFromFile // SomeHaskell

    val engine =
        Engine(
            h.query,
            { q, s -> EnumerateOneAST(s, q, h.oracle, configuration, logger) },
            namesPerRound = configuration.namesPerRound
        )
    // TODO oracle should be in query, numsols in config

    engine.search().take(1).forEach { logger.log("FIRST SOLUTION: ${it.asMap()}") }
    logger.finish()
    TODO(
        "We can't just take the first result, need to do all of them. Large search tree wraps small search tree" +
                "Also we should use conservative fast forward every once in a while or every time idk"
    )
}

// TODO this is kind of a dummy config, only gets used for logging

data class Configuration(
    val test: Test,
    val runCVC: Boolean,
    val sizeBound: Int,
    val depthBound: Int,
    val namesPerRound: Int
) : Config {
    override fun toString(): String =
        listOf(
            test.name,
            "Running CVC: $runCVC",
            "Size bound: $sizeBound",
            "Depth bound: $depthBound",
            "Names per round: $namesPerRound"
        )
            .joinToString(separator = "\n", postfix = "\n=====\n")
}
