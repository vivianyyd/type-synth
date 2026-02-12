package oneast

import query.App
import query.Example
import query.Examples
import query.Name
import util.Logger
import kotlin.math.min

typealias SearchProvider = (SearchState, Examples) -> Search

class Engine(
    startingExamples: Examples,
    private val searchProvider: SearchProvider,
    private val languageGroundTruth: (Example) -> Boolean,
    private val logger: Logger,
    private val namesPerRound: Int
) {
    private val names = startingExamples.names
    private val posExamples = startingExamples.posNoSubexprs.toMutableList()
    private val negExamples = startingExamples.neg.toMutableList()

    // ceiling division
    private val numRounds = (names.size + namesPerRound - 1) / namesPerRound
    private val scheduled = mutableListOf<Set<String>>()

    init {
        while (scheduled.size < numRounds) {
            scheduled.add(
                Selector()
                    .select(
                        // whether a name occurs in subexprs is good signal for its
                        // importance.
                        startingExamples.posWithSubexprs,
                        names,
                        buildSet { scheduled.forEach { addAll(it) } },
                        namesPerRound
                    )
            )
        }
    }

    /** Returns the next synthesis problem, or null if we are done. */
    private fun buildNextQuery(state: SearchState): Pair<Examples, SearchState>? {
        if (names.size == state.names.size) return null

        val scheduledRound = scheduled[state.names.size / namesPerRound].toList()
        // TODO I think enumeration doesn't actually need the subexprs, so we should make a separate
        //   query type which contains only maximal examples so we don't waste so much space
        val oldSize = state.names.size
        val newSize = oldSize + scheduledRound.size
        val newNames = state.names + (scheduledRound.zip(oldSize until newSize))

        fun takeExs(exs: Collection<Example>) = exs.filter { newNames.keys.containsAll(it.names) }
        val nextExamples = Examples(takeExs(posExamples), takeExs(negExamples))

        fun nameIsApplied(name: String) =
            nextExamples.posWithSubexprs.any { ex ->
                ex is App && ex.fn is Name && ex.fn.name == name
            }

        val nextState =
            SearchState(
                names = newNames,
                types =
                List(newSize) { i ->
                    if (i < oldSize) state.types[i]
                    // Importantly, we force names that are applied to be Arrows
                    // and names that are not to be labels.
                    else if (nameIsApplied(scheduledRound[i - oldSize]))
                        Arrow(TypeHole(), TypeHole())
                    else Blank(labelOnly = true)
                },
                rounds = state.rounds + oldSize,
                labelArities = state.labelArities
            )

        return nextExamples to nextState
    }

    private fun solveQuery(examples: Examples, state: SearchState): Sequence<SearchState> {
        val solver = searchProvider(state, examples)
        return solver.solutions()
    }

    private fun searchRec(state: SearchState): Sequence<SearchState> = sequence {
        val nextQueryAndSeed = buildNextQuery(state)

        if (nextQueryAndSeed == null) {
            yield(state)
            return@sequence
        }

        for (solution in solveQuery(nextQueryAndSeed.first, nextQueryAndSeed.second)) {
            logger.log("Potential solution: $solution")
            logger.log("Looking for counterexamples")
            val ctrex =
                CEGISCheck(nextQueryAndSeed.first, solution, languageGroundTruth) { s,
                                                                                    e ->
                    OneUnification(s, listOf(e)).ok()
                }
                    .counterexample()
            if (ctrex == null) {
                logger.log("Found no counterexamples")
                yieldAll(searchRec(solution))
            } else {
                logger.log("Adding counterexample ${ctrex.first}\tPosex: ${ctrex.second}")
                logger.log("Sanity check OK: ${ctrex.second == OneUnification(solution, listOf(ctrex.first)).ok()}")
                if (ctrex.second) posExamples.add(ctrex.first) else negExamples.add(ctrex.first)
            }
        }
    }

    fun search(): Sequence<SearchState> = searchRec(SearchState.emptyState)
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
    ): Set<String> {
        val scorer = Scorer(examples)
        val available = allNames.filterNot { fixed.contains(it) }
        return greedy(fixed, available, scorer, k)
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
    fun countFullyCovered(): Int {
        var count = 0
        for (i in 0 until m) {
            if (coverage[i] >= examples[i].names.size) count++
        }
        return count
    }
}
