package oneast

import oneast.searchstrategies.DFSEnumerator
import oneast.searchstrategies.SearchStrategy
import query.AbstractQuery
import query.Example
import query.Examples
import util.Config
import util.Logger
import util.io.cvc.clearCVC
import util.io.parseTest
import util.lines

fun main() {
    val testName = "dictchain"
    val query = parseTest(testName)
    val languageGroundTruth: (Example) -> Boolean = { e -> TODO() }

    val configuration =
        Configuration(
            name = testName,
            searchStrategy = ::DFSEnumerator,
            sizeBound = 20,
            depthBound = 4,
            namesPerRound = 10,
            numSols = Solutions.NumSolutions(1)
        )

    val logger =
        Logger(
            configuration = configuration, logFilename = "tmp.log", logToFile = true, verbosity = 5
        )

    run(query, languageGroundTruth, configuration, logger)
}

fun run(
    query: AbstractQuery,
    languageGroundTruth: (Example) -> Boolean,
    configuration: Configuration,
    logger: Logger
): List<SearchState> {
    clearCVC()

    val engine = Engine(query, languageGroundTruth, configuration, logger)

    val solutions = mutableListOf<SearchState>()

    when (configuration.numSols) {
        Solutions.AllSolutions -> engine.search()
        is Solutions.NumSolutions -> engine.search().take(configuration.numSols.value)
    }.forEach {
        logger.log("SOLUTION: ${it.asMap()}")
        solutions.add(it)
    }
    logger.finish()
    return solutions
}

data class Configuration(
    val name: String,
    val searchStrategy: (Examples, Boolean, Boolean, Int, Int, Logger) -> SearchStrategy,
    val sizeBound: Int,
    val depthBound: Int,
    val namesPerRound: Int,
    val numSols: Solutions
) : Config {
    override fun toString(): String =
        listOf(
            name,
            "Search strategy: $searchStrategy",
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
