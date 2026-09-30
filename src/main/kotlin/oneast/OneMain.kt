package oneast

import bench.Debug
import oneast.searchstrategies.DFSEnumerator
import oneast.searchstrategies.SearchStrategy
import query.AbstractQuery
import query.Examples
import util.GroundTruth

fun run(
    query: AbstractQuery,
    languageGroundTruth: GroundTruth,
    configuration: Configuration,
): List<SearchState> {
    val engine = Engine(query, languageGroundTruth::valid, configuration)

    val solutions = mutableListOf<SearchState>()

    when (configuration.numSols) {
        Solutions.AllSolutions -> engine.search()
        is Solutions.NumSolutions -> engine.search().take(configuration.numSols.value)
    }.forEach {
        Debug.log { "SOLUTION: ${it.asMap()}" }
        solutions.add(it)
    }
    return solutions
}

sealed interface SchedulingInfo

object SingleRound : SchedulingInfo {
    override fun toString() = "SingleRound"
}

data class Auto(val namesPerRound: Int = 5) : SchedulingInfo

data class CustomSchedule(val customSchedule: List<List<String>>) : SchedulingInfo

/** How the search fills holes. */
enum class SearchStrategyKind {
    DFS {
        override fun create(
            examples: Examples,
            emitLabelBlanks: Boolean,
            emitConstructors: Boolean,
            sizeBound: Int,
            depthBound: Int,
            soundExpansions: Boolean
        ) =
            DFSEnumerator(
                examples, emitLabelBlanks, emitConstructors, sizeBound, depthBound, soundExpansions
            )
    };

    abstract fun create(
        examples: Examples,
        emitLabelBlanks: Boolean,
        emitConstructors: Boolean,
        sizeBound: Int,
        depthBound: Int,
        soundExpansions: Boolean
    ): SearchStrategy
}

/**
 * Everything that picks between versions of the search. Keep it plain data: benchmarks record it
 * as it is, so an option that is not in here cannot be told apart from another in the results.
 */
data class Configuration(
    val searchStrategy: SearchStrategyKind = SearchStrategyKind.DFS,
    val sizeBound: Int,
    val depthBound: Int,
    val scheduleInfo: SchedulingInfo = Auto(5),
    val numSols: Solutions,
    /**
     * Whether a hole that nothing constrains may also become an arrow, and, after outlining, any
     * label. Without this, such a hole only becomes a label blank or a variable, which is faster
     * but can miss solutions.
     */
    val soundExpansions: Boolean = false,
)

sealed class Solutions {
    object AllSolutions : Solutions() {
        override fun toString() = "all"
    }

    data class NumSolutions(val value: Int) : Solutions() {
        override fun toString() = "$value"
    }
}
