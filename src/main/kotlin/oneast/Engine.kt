package oneast

import bench.Count
import bench.Debug
import bench.Phase
import bench.Stats
import query.*
import kotlin.math.min

class Engine(
    private val query: AbstractQuery,
    private val languageGroundTruth: (Example) -> Boolean,
    private val config: Configuration,
) {
    private val names = query.examples.names
    private val posExamples = query.examples.posWithSubexprs.toMutableList()
    private val negExamples = query.examples.neg.toMutableList()

    private val committedSeed = query.committedSeed.commitAll()
    private val committedNames = committedSeed.names.keys
    private val newNames = names.filter { it !in committedNames }

    private val scheduled = mutableListOf<List<String>>()

    init {
        when (val info = config.scheduleInfo) {
            is CustomSchedule -> {
                val scheduledNames = info.customSchedule.flatten()
                val scheduledNamesSet = scheduledNames.toSet()
                require(scheduledNames.size == scheduledNamesSet.size) {
                    "Duplicate name in custom schedule"
                }
                require(scheduledNamesSet.intersect(committedNames).isEmpty()) {
                    "Custom schedule includes already-committed names: " +
                            "${scheduledNamesSet.intersect(committedNames)}"
                }
                require((scheduledNamesSet + committedNames).containsAll(names)) {
                    "Schedule + committed seed are missing names: " +
                            "${names.toSet() - (scheduledNamesSet + committedNames)}"
                }
                scheduled.addAll(info.customSchedule)
            }
            is Auto -> {
                val functionNames = functions(committedSeed, newNames, query.examples.posNoSubexprs)
                val (fns, nullaries) = newNames.partition { it in functionNames }
                val numRounds = (newNames.size + info.namesPerRound - 1) / info.namesPerRound
                while (scheduled.size < numRounds) {
                    scheduled.add(
                        Selector()
                            .select(
                                // whether a name occurs in subexprs is good signal for its
                                // importance.
                                query.examples.posWithSubexprs,
                                fns,
                                buildSet { scheduled.forEach { addAll(it) } },
                                info.namesPerRound
                            )
                    )
                }
                if (scheduled.isNotEmpty()) {
                    scheduled[0] = scheduled[0] + nullaries
                } else if (nullaries.isNotEmpty()) {
                    scheduled.add(nullaries)
                }
            }
            is SingleRound -> if (newNames.isNotEmpty()) scheduled.add(newNames)
        }
        Stats.note("schedule", scheduled.toList())
        Debug.log { "Schedule: $scheduled" }
    }

    /**
     * The names among [newNames] that [examples] use as functions, given [state]'s types: those
     * whose type unification makes an arrow when it starts as a hole. That includes a name applied
     * under another name, as f is in `let g = f in g x`, and one passed where a function is
     * expected.
     */
    private fun functions(state: SearchState, newNames: List<String>, examples: List<Example>): Set<String> {
        val holes = newNames.associateWith { TypeHole() }
        val check = OneUnification(extend(state, newNames, holes::getValue), examples)
        return newNames.filterTo(HashSet()) { check.holeConstructor(holes.getValue(it)) == HoleConstructor.Arrow }
    }

    /** [state] with [newNames] added after its names, each with the type [type] gives it. */
    private fun extend(state: SearchState, newNames: List<String>, type: (String) -> Type): SearchState {
        val oldSize = state.names.size
        return SearchState(
            names = state.names + newNames.zip(oldSize until oldSize + newNames.size),
            types = state.types + newNames.map(type),
            labelArities = state.labelArities,
            numCommittedTypes = state.numCommittedTypes,
            committedLabels = state.committedLabels
        )
    }

    /** Returns the next synthesis problem, or null if we are done. */
    private fun buildNextQuery(state: SearchState, round: Int): Pair<Examples, SearchState>? {
        if (round >= scheduled.size) return null

        val scheduledRound = scheduled[round]
        // TODO I think enumeration doesn't actually need the subexprs, so we should make a separate
        //   query type which contains only maximal examples so we don't waste so much space
        val known = state.names.keys + scheduledRound

        fun takeExs(exs: Collection<Example>) = exs.filter { known.containsAll(it.names) }
        val nextExamples = Examples(takeExs(posExamples), takeExs(negExamples))

        // Importantly, we force names used as functions to be Arrows and the others to be labels.
        val functionNames = functions(state, scheduledRound, nextExamples.posNoSubexprs)
        val nextState =
            extend(state, scheduledRound) {
                if (it in functionNames) Arrow(TypeHole(), TypeHole()) else Blank(labelOnly = true)
            }

        return nextExamples to nextState
    }

    private fun searchRec(state: SearchState, round: Int, outerDepthBound: Int): Sequence<SearchState> = sequence {
        val nextQueryAndSeed = buildNextQuery(state, round)

        if (nextQueryAndSeed == null) {
            yield(state)
            return@sequence
        }
        Debug.log { "Current query: ${nextQueryAndSeed.second} with depth bound $outerDepthBound" }
        val statsId =
            Stats.newSearch(
                round,
                outerDepthBound,
                scheduled[round],
                nextQueryAndSeed.first.posNoSubexprs.size,
                nextQueryAndSeed.first.neg.size
            )
        val search =
            Search(
                nextQueryAndSeed.second,
                nextQueryAndSeed.first,
                query.oracle,
                config.copy(depthBound = outerDepthBound),
                statsId
            )

        for (solution in search.solutions()) {
            Debug.log { "Looking for counterexamples for potential solution $solution" }
            val ctrex =
                Stats.phase(statsId, Phase.CEGIS) {
                    CEGISCheck(nextQueryAndSeed.first, solution, languageGroundTruth) { s, e ->
                        OneUnification(s, listOf(e)).ok
                    }
                        .counterexample()
                        ?.also { Stats.inc(if (it.second) Count.CEGIS_POS else Count.CEGIS_NEG) }
                }
            if (ctrex == null) {
                Debug.log { "Found no counterexamples" }
                yieldAll(searchRec(solution, round + 1, outerDepthBound))
            } else {
                Debug.log { "Adding ${if (ctrex.second) "+" else "-"} counterexample ${ctrex.first}" }
                Stats.event(
                    "counterexample",
                    mapOf("search" to statsId, "positive" to ctrex.second, "example" to ctrex.first)
                )
                if (ctrex.second) posExamples.add(ctrex.first) else negExamples.add(ctrex.first)
            }
        }
    }

    fun search(): Sequence<SearchState> =
        (0 until config.depthBound).asSequence().flatMap { searchRec(committedSeed, round = 0, it) }
}

/*
Another option that could've worked:
Partitioning examples: Pick random example, take set of all constructs in that example.
Take all examples that involve only those constructs. if examples not big enough add examples
that add fewest num new constructs. Or, for each new name, which has the fewest edges to
other names not in my set? (did that sentence make sense)
Can use universe of examples to guide in finding initial set of names with enough support of
self contained examples.
If we start with 100 examples, want a subset of names for which i can find 20 examples.
 */
private class Selector {
    /** Requires: [candidates] and [base] are disjoint. */
    private fun greedy(
        base: Set<String>, // already chosen elements
        candidates: List<String>, // universe to select from
        scorer: Scorer,
        k: Int, // number of elements to add
    ): Set<String> {
        if (candidates.size <= k) return candidates.toSet()

        // Initialize coverage from base
        for (name in base) {
            scorer.addName(name)
        }
        val added = mutableSetOf<String>()
        while (added.size < k) {
            var bestName: String? = null
            var bestGain = 0.0
            for (name in candidates) {
                if (added.contains(name)) continue
                val gain = scorer.marginalGain(name)
                if (gain > bestGain) {
                    bestGain = gain
                    bestName = name
                }
            }
            if (bestName == null)
                break // this only occurs when none of the names appear in any example
            scorer.addName(bestName)
            added.add(bestName)
        }
        return added
    }

    fun select(
        examples: List<Example>,
        allNames: List<String>,
        fixed: Set<String>,
        k: Int,
    ): List<String> {
        val scorer = Scorer(examples)
        val available = allNames.filterNot { fixed.contains(it) }
        return greedy(fixed, available, scorer, k).toList()
    }
}

/**
 * Scorer with coverage counts. Computes the marginal gain of adding a named component to the set.
 * Uses the invariant that [marginalGain] is only called on names that have not yet been added to
 * the set, so counting coverage of each example suffices to compute gain.
 */
private class Scorer(private val examples: List<Example>) {
    private val m = examples.size

    // For each example, number of elements already chosen
    val coverage = IntArray(m)

    // Precompute which examples contain each name
    val nameToExamples: Map<String, List<Int>> = run {
        val map = mutableMapOf<String, MutableList<Int>>()
        for ((i, ex) in examples.withIndex()) {
            for (name in ex.names) {
                map.computeIfAbsent(name) { mutableListOf() }.add(i)
            }
        }
        map
    }

    // relaxed score using coverage counts
    fun score(): Double {
        var total = 0.0
        for (i in 0 until m) {
            total += min(coverage[i].toDouble() / examples[i].names.size, 1.0)
        }
        return total
    }

    // marginal gain of adding a candidate name
    fun marginalGain(name: String): Double {
        var gain = 0.0
        val indices = nameToExamples[name] ?: return 0.0
        for (i in indices) {
            if (coverage[i] < examples[i].names.size) {
                val before = coverage[i].toDouble() / examples[i].names.size
                val after = (coverage[i] + 1).toDouble() / examples[i].names.size
                gain += min(after, 1.0) - min(before, 1.0)
            }
        }
        return gain
    }

    // add a name and update coverage counts
    fun addName(name: String) {
        val indices = nameToExamples[name] ?: return
        for (i in indices) {
            coverage[i]++
        }
    }

    // true objective: number of fully covered examples
}
