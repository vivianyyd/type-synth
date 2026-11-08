package oneast

import bench.Count
import bench.Debug
import bench.Phase
import bench.Stats
import query.*
import util.GroundTruth
import util.MemoizedGroundTruth
import util.ObservationalEquivalenceOracle
import util.Oracle
import util.TimedOracle
import kotlin.math.min

class Engine(
    private val query: AbstractQuery,
    private val languageGroundTruth: GroundTruth,
    private val config: Configuration,
) {
    private val names = query.examples.names
    private val posExamples = query.examples.posWithSubexprs.toMutableList()
    private val negExamples = query.examples.neg.toMutableList()

    private val committedSeed = query.committedSeed.commitAll()
    private val committedNames = committedSeed.names.keys
    private val newNames = names.filter { it !in committedNames }

    private val scheduled = mutableListOf<List<String>>()

    // The ground truth can be slow (e.g. a compiler call), and the observational oracle asks it about
    // the same expressions over and over, across rounds too.
    private val memoizedGroundTruth = MemoizedGroundTruth(languageGroundTruth)

    // Built from all the examples so far, so it is rebuilt whenever a counterexample is added
    private var observationalOracle: ObservationalEquivalenceOracle? = null

    private fun oracle(): Oracle =
        TimedOracle(
            when (config.oracle) {
                OracleKind.Types -> query.oracle
                OracleKind.Observational ->
                    observationalOracle
                        ?: ObservationalEquivalenceOracle(
                            Examples(posExamples, negExamples), memoizedGroundTruth
                        )
                            .also { observationalOracle = it }
            }
        )

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
        Stats.note("schedule", scheduled.toList())
        Debug.log { "Schedule: $scheduled" }
    }

    private fun nameIsApplied(name: String, exs: Examples): Boolean {
        fun nameAppliedIn(ex: Example): Boolean = when (ex) {
            is Name -> false
            is App -> ((ex.fn is Name && ex.fn.name == name) ||
                    (nameAppliedIn(ex.fn) || nameAppliedIn(ex.arg)))
        }
        return exs.posNoSubexprs.any { nameAppliedIn(it) }
    }

    /** Returns the synthesis problem of [step], or null if the schedule has no rounds left. */
    private fun buildNextQuery(step: Step): Pair<Examples, SearchState>? {
        if (step.rounds.first >= scheduled.size) return null

        val state = step.seed
        val scheduledRound = names(step)
        // TODO I think enumeration doesn't actually need the subexprs, so we should make a separate
        //   query type which contains only maximal examples so we don't waste so much space
        val oldSize = state.names.size
        val newSize = oldSize + scheduledRound.size
        val newNames = state.names + (scheduledRound.zip(oldSize until newSize))

        fun takeExs(exs: Collection<Example>) = exs.filter { newNames.keys.containsAll(it.names) }
        val nextExamples = Examples(takeExs(posExamples), takeExs(negExamples))

        val nextState =
            SearchState(
                names = newNames,
                types =
                List(newSize) { i ->
                    if (i < oldSize) state.types[i]
                    // Importantly, we force names that are applied to be Arrows
                    // and names that are not to be labels.
                    else if (nameIsApplied(scheduledRound[i - oldSize], nextExamples))
                        Arrow(TypeHole(), TypeHole())
                    else Blank(labelOnly = true)
                },
                labelArities = state.labelArities,
                numCommittedTypes = state.numCommittedTypes,
                // A round never changes an earlier round's labels, not even their arities. When
                // it needs two of them to be one label, see resolveClashes.
                committedLabels = state.labelArities.keys
            )

        return nextExamples to nextState
    }

    private fun names(step: Step) = step.rounds.flatMap { scheduled[it] }

    /**
     * The solutions that solve the last step of [path] and then the rest of the schedule. Each step
     * of [path] is seeded by a solution of the step before it. The step tries each outer depth bound
     * in [depths] in turn, skipping solutions a smaller bound found, and resolves the clashes of all
     * of them only after that. [resolved] holds the merged steps already searched in this call of
     * [search], by their seed's [SearchState.id] and rounds, with what each search found out.
     * [outcome] gets what this call found out.
     */
    private fun searchRec(
        path: List<Step>,
        depths: IntRange,
        extraArities: Int,
        resolved: MutableMap<Pair<Int, IntRange>, Outcome>,
        outcome: Outcome,
    ): Sequence<SearchState> = sequence {
        val i = path.lastIndex
        val step = path.last()
        val nextQueryAndSeed = buildNextQuery(step)

        if (nextQueryAndSeed == null) {
            outcome.solved = true
            yield(step.seed)
            return@sequence
        }
        val found = mutableListOf<SearchState>()
        val clashes = mutableSetOf<Set<Int>>()
        // Whether this step has a solution depends only on the types of the names its examples use
        val conflicts = dependencies(path, nextQueryAndSeed.first).toMutableSet()
        depths@ for (outerDepthBound in depths) {
            Debug.log { "Current query: ${nextQueryAndSeed.second} with depth bound $outerDepthBound" }
            val statsId =
                Stats.newSearch(
                    step.rounds.first,
                    outerDepthBound,
                    names(step),
                    nextQueryAndSeed.first.posNoSubexprs.size,
                    nextQueryAndSeed.first.neg.size
                )
            val search =
                Search(
                    nextQueryAndSeed.second,
                    nextQueryAndSeed.first,
                    oracle(),
                    config.copy(depthBound = outerDepthBound),
                    statsId,
                    extraArities
                )

            for (solution in search.solutions()) {
                if (found.any { it.equivalentTo(solution) }) continue
                found.add(solution)
                Debug.log { "Looking for counterexamples for potential solution $solution" }
                val ctrex =
                    Stats.phase(statsId, Phase.CEGIS) {
                        CEGISCheck(nextQueryAndSeed.first, solution, languageGroundTruth::valid) { s, e ->
                            OneUnification(s, listOf(e)).ok
                        }
                            .counterexample()
                            ?.also { Stats.inc(if (it.second) Count.CEGIS_POS else Count.CEGIS_NEG) }
                    }
                if (ctrex == null) {
                    Debug.log { "Found no counterexamples" }
                    val next = step.rounds.last + 1
                    val rest = Outcome()
                    yieldAll(searchRec(path + Step(solution, next..next), depths, extraArities, resolved, rest))
                    if (rest.solved) outcome.solved = true
                    else if (config.backjump && i !in rest.conflicts && !outcome.solved) {
                        // The rest fails whatever this step's solution is: go back to the latest step
                        // it depends on, skipping this step's other solutions
                        Stats.inc(Count.BACKJUMPS)
                        Stats.event("backjump", mapOf("from" to i, "to" to rest.conflicts.maxOrNull()))
                        conflicts.clear()
                        conflicts += rest.conflicts
                        clashes += search.clashes
                        break@depths
                    } else conflicts += rest.conflicts - i
                } else {
                    Debug.log { "Adding ${if (ctrex.second) "+" else "-"} counterexample ${ctrex.first}" }
                    Stats.event(
                        "counterexample",
                        mapOf("search" to statsId, "positive" to ctrex.second, "example" to ctrex.first)
                    )
                    if (ctrex.second) posExamples.add(ctrex.first) else negExamples.add(ctrex.first)
                    observationalOracle = null
                }
            }
            clashes += search.clashes
        }

        yieldAll(resolveClashes(path, clashes, depths, extraArities, resolved, outcome, conflicts))
        outcome.conflicts += if (outcome.solved) (0 until i).toSet() else conflicts
    }

    /**
     * The steps of [path] before its last whose names are used by those of [examples] that use the
     * last step's names. The other examples use only earlier steps' names, whose types are fixed.
     */
    private fun dependencies(path: List<Step>, examples: Examples): Set<Int> {
        val own = names(path.last()).toSet()
        val used =
            (examples.posNoSubexprs + examples.neg)
                .map { it.names }
                .filter { names -> names.any { it in own } }
                .flatten()
                .toSet()
        return path.indices.filter { j -> j < path.lastIndex && names(path[j]).any { it in used } }.toSet()
    }

    /**
     * [clashes] are sets of labels that the last step of [path] needed to be equal. For each, searches
     * the steps from the one that created the earliest of its labels to the last again, as one step:
     * the fewest steps first. A clash only between labels of the committed seed or of the last step
     * has no steps to search again.
     *
     * An earlier step's examples may not have forced two values to share a label that a later step
     * needs them to share. Searching both steps as one, from a seed without those labels, lets the
     * values get one label without any step changing a label it was given.
     *
     * Marks [outcome] solved if one of the searches is, and adds to [conflicts] the steps the
     * failures of the others depend on.
     */
    private fun resolveClashes(
        path: List<Step>,
        clashes: Set<Set<Int>>,
        depths: IntRange,
        extraArities: Int,
        resolved: MutableMap<Pair<Int, IntRange>, Outcome>,
        outcome: Outcome,
        conflicts: MutableSet<Int>,
    ): Sequence<SearchState> = sequence {
        // The labels each step created: those in the next step's seed but not its own
        val created = path.zipWithNext { s, next -> next.seed.labelArities.keys - s.seed.labelArities.keys }
        val clashesByStart =
            clashes.groupBy { labels -> created.indexOfFirst { it.any { l -> l in labels } } }
                .filterKeys { it >= 0 }
                .toSortedMap(reverseOrder())
        for ((start, startClashes) in clashesByStart) {
            val merged = Step(path[start].seed, path[start].rounds.first..path.last().rounds.last)
            val again = resolved[merged.seed.id to merged.rounds]
            if (again != null) {
                // Searched already, from the same seed, so it ends the same way
                if (again.solved) outcome.solved = true else conflicts += again.conflicts
                continue
            }
            Stats.inc(Count.RESOLVES)
            Stats.event(
                "resolve",
                mapOf("from" to merged.rounds.first, "to" to merged.rounds.last, "clashes" to startClashes)
            )
            Debug.log { "Clashes $startClashes: searching rounds ${merged.rounds} again as one" }
            val outcomeOfMerged = Outcome().also { resolved[merged.seed.id to merged.rounds] = it }
            yieldAll(searchRec(path.take(start) + merged, depths, extraArities, resolved, outcomeOfMerged))
            if (outcomeOfMerged.solved) outcome.solved = true else conflicts += outcomeOfMerged.conflicts
        }
    }

    /**
     * Each outer depth bound in turn, or with [Configuration.depthPerRound] all of them in each round.
     * Only if none of them gives a solution, again with labels allowed one more parameter than the
     * solver's bounds, and so on up to [Configuration.extraArities]: the bounds come from heuristics,
     * which can be too low. A round with no solution at a small depth bound is common, and fails fast
     * only with the solver's bounds, so the extra arities wait until every depth bound has failed.
     */
    fun search(): Sequence<SearchState> = sequence {
        val extras = if (config.labelArities is LabelArities.Solved) 0..config.extraArities else 0..0
        val passes =
            if (config.depthPerRound) listOf(0 until config.depthBound)
            else (0 until config.depthBound).map { it..it }
        for (extra in extras) {
            if (extra > 0) {
                Debug.log { "No solution with label arities up to the solver's bounds + ${extra - 1}" }
                Stats.event("extraArities", mapOf("extra" to extra))
            }
            var found = false
            for (depths in passes) {
                val path = listOf(Step(committedSeed, 0..0))
                for (solution in searchRec(path, depths, extra, resolved = HashMap(), Outcome())) {
                    found = true
                    yield(solution)
                }
            }
            if (found) return@sequence
        }
    }
}

/**
 * Rounds [rounds] of the schedule, searched as one round from [seed]. One round, unless
 * [Engine.resolveClashes] merged several.
 */
private class Step(val seed: SearchState, val rounds: IntRange)

/** What a call of [Engine.searchRec] found out about the last step of its path. */
private class Outcome {
    /** Whether it yielded a solution. */
    var solved = false

    /**
     * If it did not, the steps of the path, by index, that its failure depends on: as long as their
     * solutions stay the same, so does the failure. All are before the last step. See
     * [Configuration.backjump].
     */
    val conflicts = mutableSetOf<Int>()
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
