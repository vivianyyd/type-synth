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

sealed interface SchedulingInfo

data class Auto(val namesPerRound: Int = 5) : SchedulingInfo {
    override fun toString() = "Auto with $namesPerRound names per round"
}

data class CustomSchedule(val customSchedule: List<List<String>>) : SchedulingInfo {
    override fun toString() = "Custom schedule: $customSchedule"
}

data class Configuration(
    val name: String,
    val searchStrategy: (Examples, Boolean, Boolean, Int, Int, Logger) -> SearchStrategy,
    val sizeBound: Int,
    val depthBound: Int,
    val scheduleInfo: SchedulingInfo = Auto(5),
    val numSols: Solutions
) : Config {
    override fun toString(): String =
        listOf(
            name,
            "Search strategy: $searchStrategy",
            "Size bound: $sizeBound",
            "Depth bound: $depthBound",
            "Schedule: $scheduleInfo",
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
