package oneast

import oneast.searchstrategies.DFSEnumerator
import query.AbstractQuery
import util.Config
import util.Logger
import util.io.parseTest
import util.lines

fun main() {
    val testName = "dictchain"
    val query = parseTest(testName)

    val configuration =
        Configuration(
            name = testName,
            runCVC = true,
            sizeBound = 20,
            depthBound = 4,
            namesPerRound = 10,
            numSols = Solutions.NumSolutions(1)
        )

    val logger =
        Logger(
            configuration = configuration, logFilename = "tmp.log", logToFile = true, verbosity = 5
        )

    run(query, configuration, logger)
    TODO(
        "We can't just take the first result, need to do all of them. Large search tree wraps small search tree" +
                "Also we should use conservative fast forward every once in a while or every time idk"
    )
}

fun run(query: AbstractQuery, configuration: Configuration, logger: Logger) {
    val engine =
        Engine(
            query.examples,
            { e, s -> Search(e, s, query.oracle, configuration, ::DFSEnumerator, logger) },
            configuration.namesPerRound
        )

    when (configuration.numSols) {
        Solutions.AllSolutions -> engine.search()
        is Solutions.NumSolutions -> engine.search().take(configuration.numSols.value)
    }.forEach { logger.log("FIRST SOLUTION: ${it.asMap()}") }
    logger.finish()
}

data class Configuration(
    val name: String,
    val runCVC: Boolean,
    val sizeBound: Int,
    val depthBound: Int,
    val namesPerRound: Int,
    val numSols: Solutions
) : Config {
    override fun toString(): String =
        listOf(
            name,
            "Running CVC: $runCVC",
            "Size bound: $sizeBound",
            "Depth bound: $depthBound",
            "Names per round: $namesPerRound",
            "Searching for $numSols solutions"
        )
            .lines() + "\n=====\n"
}

sealed class Solutions {
    object AllSolutions : Solutions() {
        override fun toString() = "all"
    }

    data class NumSolutions(val value: Int) : Solutions() {
        override fun toString() = "$value"
    }
}
