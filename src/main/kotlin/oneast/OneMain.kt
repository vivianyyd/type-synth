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
    val engine = Engine(query, languageGroundTruth, configuration)

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
            expansions: Expansions,
            clashes: MutableSet<Set<Int>>?
        ) =
            DFSEnumerator(
                examples, emitLabelBlanks, emitConstructors, sizeBound, depthBound, expansions, clashes
            )
    };

    abstract fun create(
        examples: Examples,
        emitLabelBlanks: Boolean,
        emitConstructors: Boolean,
        sizeBound: Int,
        depthBound: Int,
        expansions: Expansions,
        clashes: MutableSet<Set<Int>>?
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
    /** What each hole may be filled with. */
    val expansions: Expansions = Expansions.Unsound,
    /** How each outline's labels get their arities before concretizing. */
    val labelArities: LabelArities = LabelArities.Solved,
    /**
     * With [LabelArities.Solved], how many parameters past the solver's bound a label may get, one
     * more at a time, when a search finds no solution within the bounds.
     */
    val extraArities: Int = 2,
    /**
     * Whether the solver may conclude that a function's result shares a variable with a parameter
     * when examples differing only in that argument's type have results of different types.
     */
    val resultDependence: Boolean = true,
    /** Which oracle answers whether two expressions have the same type. */
    val oracle: OracleKind = OracleKind.Types,
    /** How a round treats the labels of the rounds before it. */
    val rounds: Rounds = Rounds.Retry,
)

enum class Rounds {
    /**
     * Earlier rounds' labels are not committed. While outlining, a round blanks out labels that
     * clash and enumerates them again, and it may give an earlier label a new arity.
     */
    Retry,

    /**
     * Each round commits to every label that exists when it starts. When labels clash, the round
     * records it and prunes. After its search, for each clash, the rounds from the one that created
     * the earliest of those labels up to this one are solved again as one round, so that the clash
     * can be resolved by giving the values one label.
     */
    ResolveOnClash,
}

enum class OracleKind {
    /** The query's own oracle, which knows the actual types. */
    Types,

    /**
     * An [util.ObservationalEquivalenceOracle] over the examples, asking the language's ground truth
     * instead of looking at types.
     */
    Observational,
}

enum class Expansions {
    /**
     * Only what unification allows. A hole that nothing constrains becomes only a label blank or a
     * variable, which is faster but can miss solutions.
     */
    Unsound,

    /**
     * Like [Unsound], but a hole that nothing constrains may also become an arrow and, after
     * outlining, any label.
     */
    Sound,

    /**
     * Ignore unification: every variable, an arrow, and every label (a label blank, while
     * outlining).
     */
    Simple,
}

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
