package oneast

import oneast.searchstrategies.SearchStrategy
import query.AbstractQuery
import query.Examples
import util.Config
import util.GroundTruth
import util.Logger
import util.io.cvc.clearCVC
import util.lines

fun run(
    query: AbstractQuery,
    languageGroundTruth: GroundTruth,
    configuration: Configuration,
    logger: Logger
): List<SearchState> {
    clearCVC()

    val engine = Engine(query, languageGroundTruth::valid, configuration, logger)

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
