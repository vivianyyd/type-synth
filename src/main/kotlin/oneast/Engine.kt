package oneast

import query.*
import util.Logger
import kotlin.math.min

class Engine(
    private val query: AbstractQuery,
    private val languageGroundTruth: (Example) -> Boolean,
    private val config: Configuration,
    private val logger: Logger
) {
    private val names = query.examples.names

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
                val (fns, nullaries) = newNames.partition { nameIsApplied(it, query.examples) }
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
        logger.log("Schedule: $scheduled")
    }

    private fun nameIsApplied(name: String, exs: Examples): Boolean {
        fun nameAppliedIn(ex: Example): Boolean = when (ex) {
            is Name -> false
            is App -> ((ex.fn is Name && ex.fn.name == name) ||
                    (nameAppliedIn(ex.fn) || nameAppliedIn(ex.arg)))
        }
        return exs.posNoSubexprs.any { nameAppliedIn(it) }
    }

    /** The set of examples for each round used during CEGIS */
    private val workingExsSubset =
        mutableMapOf<Int, Pair<MutableList<Example>, MutableList<Example>>>()

    private fun toExamples(e: Pair<List<Example>, List<Example>>) = Examples(e.first, e.second)

    /** Returns the next synthesis problem, or null if we are done. */
    private fun buildNextQuery(state: SearchState, round: Int): Pair<Examples, SearchState>? {
        if (round >= scheduled.size) return null

        val scheduledRound = scheduled[round]
        // TODO I think enumeration doesn't actually need the subexprs, so we should make a separate
        //   query type which contains only maximal examples so we don't waste so much space
        val oldSize = state.names.size
        val newSize = oldSize + scheduledRound.size
        val newNames = state.names + (scheduledRound.zip(oldSize until newSize))

        fun takeExs(exs: Collection<Example>) = exs.filter { newNames.keys.containsAll(it.names) }
        val allNextExamples = Examples(takeExs(query.examples.posWithSubexprs), takeExs(query.examples.neg))

        val nextState =
            SearchState(
                names = newNames,
                types =
                List(newSize) { i ->
                    if (i < oldSize) state.types[i]
                    // Importantly, we force names that are applied to be Arrows
                    // and names that are not to be labels.
                    else if (nameIsApplied(scheduledRound[i - oldSize], allNextExamples))
                        Arrow(TypeHole(), TypeHole())
                    else Blank(labelOnly = true)
                },
                labelArities = state.labelArities,
                numCommittedTypes = state.numCommittedTypes,
                committedLabels = state.committedLabels)

        fun takeSmallest(exs: Collection<Example>): MutableList<Example> {
            val e = exs.sortedBy { it.size() }
            return e.take((e.size / 3).coerceAtLeast(e.filter{it is Name}.size + 5)).toMutableList()
        }
        val nextExamples = toExamples(workingExsSubset.getOrPut(round) {
            takeSmallest(allNextExamples.posWithSubexprs) to
                    takeSmallest(allNextExamples.neg)
        })

        return nextExamples to nextState
    }

    private fun solveQuery(examples: Examples, state: SearchState, outerDepthBound: Int): Sequence<SearchState> {
        val solver = Search(state, examples, query.oracle, config.copy(depthBound = outerDepthBound), logger)
        return solver.solutions()
    }

    private fun searchRec(state: SearchState, round: Int, outerDepthBound: Int): Sequence<SearchState> = sequence {
        val nextQueryAndSeed = buildNextQuery(state, round)

        if (nextQueryAndSeed == null) {
            yield(state)
            return@sequence
        }
        logger.log("Current query: ${nextQueryAndSeed.second} with depth bound $outerDepthBound")

        for (solution in solveQuery(nextQueryAndSeed.first, nextQueryAndSeed.second, outerDepthBound)) {
            logger.log("Looking for counterexamples for potential solution $solution")
            val ctrex =
                CEGISCheck(
                    toExamples(
                        query.examples.posWithSubexprs.filter { nextQueryAndSeed.second.names.keys.containsAll(it.names) } to
                                query.examples.neg.filter { nextQueryAndSeed.second.names.keys.containsAll(it.names) }
                    ), solution, languageGroundTruth) { s, e ->
                    OneUnification(s, listOf(e)).ok
                }.counterexample()
            if (ctrex == null) {
                logger.log("Found no counterexamples")
                yieldAll(searchRec(solution, round + 1, outerDepthBound))
            } else {
                logger.log("Adding ${if (ctrex.second) "+" else "-"} counterexample ${ctrex.first}")
                if (ctrex.second) workingExsSubset[round]!!.first.add(ctrex.first)
                else workingExsSubset[round]!!.second.add(ctrex.first)
//                if (ctrex.second) posExamples.add(ctrex.first) else negExamples.add(ctrex.first)
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
    fun countFullyCovered(): Int {
        var count = 0
        for (i in 0 until m) {
            if (coverage[i] >= examples[i].names.size) count++
        }
        return count
    }
}
