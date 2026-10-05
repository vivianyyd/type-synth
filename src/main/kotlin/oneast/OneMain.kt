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
            soundExpansions: Boolean,
            labelsGiven: Boolean
        ) =
            DFSEnumerator(
                examples, emitLabelBlanks, emitConstructors, sizeBound, depthBound, soundExpansions,
                labelsGiven
            )
    };

    abstract fun create(
        examples: Examples,
        emitLabelBlanks: Boolean,
        emitConstructors: Boolean,
        sizeBound: Int,
        depthBound: Int,
        soundExpansions: Boolean,
        labelsGiven: Boolean
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
    /** How each outline's labels get their arities before concretizing. */
    val labelArities: LabelArities = LabelArities.Solved,
    /**
     * The labels the search may use, mapped to their arities. With these, the search neither
     * outlines nor picks label arities: it concretizes from the start, and a hole nothing
     * constrains may become any of these labels. Null: the search makes up labels as it outlines.
     */
    val givenLabels: Map<Int, Int>? = null,
)

sealed class LabelArities {
    /**
     * Ask the solver, per outline, how many parameters each label could need, then try every
     * arity from 0 up to that.
     */
    object Solved : LabelArities()

    /** No solver: try every arity from 0 to [bound] for each label. */
    data class Deepened(val bound: Int) : LabelArities()
}

sealed class Solutions {
    object AllSolutions : Solutions() {
        override fun toString() = "all"
    }

    data class NumSolutions(val value: Int) : Solutions() {
        override fun toString() = "$value"
    }
}
