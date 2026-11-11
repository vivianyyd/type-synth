package oneast

import bench.*
import dependencyanalysis.ParameterwiseDependencyAnalysis
import query.Examples
import util.*
import java.util.stream.Collectors

/**
 * Lazily produces ALL solutions for [examples] from this [seed]. Charges its work to search
 * [statsId] (see [Stats.newSearch]). With [LabelArities.Solved], each label may have up to
 * [extraArities] more parameters than the solver's bound for it.
 */
class Search(
    private val seed: SearchState,
    private val examples: Examples,
    private val oracle: Oracle,
    private val config: Configuration,
    private val statsId: Int = -1,
    private val extraArities: Int = 0,
) {
    /**
     * The sets of labels that the positive examples needed to be equal, in the states searched so
     * far.
     */
    val clashes: Set<Set<Int>>
        get() = recordedClashes

    private val recordedClashes = HashSet<Set<Int>>()

    private fun allCandidates(
        c: SearchState,
        emitLabelBlanks: Boolean,
        emitConstructors: Boolean,
        sizeBound: Int,
        depthBound: Int,
        onClash: (Set<Int>) -> Unit = { recordedClashes.add(it) },
    ): Sequence<SearchState> =
        config.searchStrategy
            .create(
                examples,
                emitLabelBlanks,
                emitConstructors,
                sizeBound,
                depthBound,
                config.expansions,
                onClash
            )
            .candidates(c)

    private fun posUnification(s: SearchState) = OneUnification(s, examples.posNoSubexprs)

    /**
     * Replaces the blanks of outline [s] with labels. Blanks in the same group get the same label:
     * the one the examples require, or else a new one.
     */
    private fun assignLabelClasses(s: SearchState): SearchState {
        val holes = s.types.flatMap { it.allHoles() }
        val blanks = holes.filterIsInstance<Blank>()
        // An outline has no type holes left. If one is here, a blank it was unified with could still
        // turn into anything, so nothing can be concluded about that blank's label.
        require(blanks.size == holes.size) { "An outline has type holes left: $s" }
        require(blanks.all { it.labelOnly })
        // The search only yields satisfiable states, so the blanks can agree on labels.
        val groups =
            posUnification(s).blankGroups() ?: error("The blanks of an outline disagree: $s")

        val freshLabel = Counter()
        freshLabel.ensureGt(s.labelArities.keys.maxOrNull() ?: -1)
        val freshLabelOfGroup = mutableMapOf<Int, Int>()

        fun getLabel(b: Blank): Int {
            val group = groups.groupOf(b)
            return groups.labelOf(group) ?: freshLabelOfGroup.getOrPut(group) { freshLabel.get() }
        }

        fun assignLabels(t: Type): Type =
            when (t) {
                is Arrow -> Arrow(assignLabels(t.l), assignLabels(t.r))
                is NamedLabel -> t.copy(params = t.params.map { assignLabels(it) })
                is Blank -> NamedLabel(label = getLabel(t), params = emptyList())
                // Its parameters come once its arity is decided, from addParamHoles
                is TypeHole -> error("Shouldn't happen")
                is Variable -> t
            }

        return s.mapTypes { assignLabels(it) }
    }

    /** The outlines of seed depth [depth], with their label classes assigned. */
    private fun outlines(depth: Int): Set<SearchState> {
        val withLabelClasses =
            Stats.phase(statsId, Phase.OUTLINE) {
                allCandidates(
                    seed,
                    emitLabelBlanks = true,
                    emitConstructors = true,
                    sizeBound = config.sizeBound,
                    depthBound = depth,
                )
                    .map {
                        Stats.inc(Count.OUTLINES)
                        assignLabelClasses(it)
                    }
                    .toSet()
            }

        Debug.log { withLabelClasses.countedLines("Seeds before label arities") }
        return withLabelClasses
    }

    /**
     * The seeds of each of [outlines], by outline: one per choice of arities for its labels, with
     * [LabelArities.Solved] those up to the solver's bounds plus [extraArities]. [merged] is whether
     * the outlines are [mergedOutlines].
     */
    private fun seeds(outlines: Set<SearchState>, merged: Boolean): Map<SearchState, List<SearchState>> =
        when (val la = config.labelArities) {
            LabelArities.Solved -> {
                val bounds = solvedArityBounds(outlines, merged)
                Stats.phase(statsId, Phase.ARITY) {
                    withArities(bounds.flatMap { (s, bound) -> arityChoices(s, bound).map { s to it } })
                }
            }
            is LabelArities.Deepened ->
                Stats.phase(statsId, Phase.ARITY) { deepenLabelArities(outlines, la.bound) }
        }

    /**
     * The outlines to search at a seed depth after those whose clashes are in [clashes]: each of
     * those with two labels that clashed while concretizing it merged into one. Leaves out those
     * already in [seen], to which it adds the rest, and those that outlining's checks reject.
     *
     * [assignLabelClasses] gives a group of blanks a new label unless the positive examples
     * determine its label. They may determine it only through another label's parameter, which
     * only concretizing fills, so the new label is wrong, and concretizing can't change it. What
     * concretizing finds is a clash between the new label and the one the group needs.
     *
     * So the outline is searched again, from before its arities, with the two labels merged: one
     * that isn't committed becomes the other, which keeps its arity if it is committed; of two that
     * aren't, the higher becomes the lower. Two committed labels are left to
     * [Engine.resolveClashes]. A merged outline gets its own arities from the solver and its own
     * concretization, and can clash and be merged again. Each merge removes a label, so this ends.
     *
     * Sound: each search is as it would be without merging, but for the merged outlines after it,
     * which are concretized and checked like any other. A merge is a label map, so positive
     * examples that passed keep passing, and a negative example that type-checked still does.
     * Complete as far as concretizing is: following a solution's fills in the unmerged outline
     * reaches a clash between two labels the solution has as one, when unifying fails or when a
     * hole is unified with both, which queues the outline one merge closer to the solution's.
     *
     * The checks hold whatever arities the solver then picks. The positive examples are checked
     * with each label that isn't committed at 0 parameters, since parameters only add constraints.
     * The negative examples are checked at 1, the hardest arity: each use of a label then has a
     * hole of its own as its parameter, which [skolemize] makes a label used nowhere else, so more
     * parameters add nothing, and 0 accept whatever 1 does.
     */
    private fun mergedOutlines(
        clashes: Map<SearchState, Set<Set<Int>>>,
        seen: MutableSet<SearchState>,
    ): Set<SearchState> =
        Stats.phase(statsId, Phase.OUTLINE) {
            clashes
                .flatMap { (outline, outlineClashes) -> outlineClashes.mapNotNull { mergeLabels(outline, it) } }
                .filterTo(LinkedHashSet()) { merged ->
                    Stats.inc(Count.MERGES)
                    val rejected =
                        when {
                            !seen.add(merged) -> Count.MERGES_DUPLICATE
                            !posUnification(withUncommittedArity(merged, 0)).satisfiable() ->
                                Count.MERGES_PRUNED_POS
                            withUncommittedArity(merged, 1).acceptsANegative(examples.neg) ->
                                Count.MERGES_PRUNED_NEG
                            else -> null
                        }
                    rejected?.let { Stats.inc(it) }
                    rejected == null
                }
                .also { Debug.log { it.countedLines("Merged outlines") } }
        }

    /**
     * Outline [s] with the two labels of [clash] as one, as [mergedOutlines] says. Null if both are
     * committed, or if [clash] isn't two labels.
     */
    private fun mergeLabels(s: SearchState, clash: Set<Int>): SearchState? {
        if (clash.size != 2) return null
        val (low, high) = clash.sorted()
        val (from, to) =
            when {
                high !in s.committedLabels -> high to low
                low !in s.committedLabels -> low to high
                else -> return null
            }

        fun merge(t: Type): Type =
            when (t) {
                is Arrow -> Arrow(merge(t.l), merge(t.r))
                is NamedLabel -> NamedLabel(if (t.label == from) to else t.label, t.params.map { merge(it) })
                is THole,
                is Variable -> t
            }

        return s.mapTypes { merge(it) }
    }

    /** Outline [s] as a seed, with each of its labels that isn't committed at [arity]. */
    private fun withUncommittedArity(s: SearchState, arity: Int): SearchState {
        val arities = s.labelArities + uncommittedLabels(s).associateWith { arity }
        return s.mapTypesAndSetLabelArities(arities) { it.addParamHoles(arities) }
    }

    private fun uncommittedLabels(s: SearchState) =
        s.types.flatMap { it.labels() }.map { it.first }.toSet() - s.committedLabels

    /**
     * Arities for [s]'s labels: committed ones keep theirs, and each other label has from 0 to its
     * bound in [bounds] + [extraArities]. None if that is below 0 for a label.
     */
    private fun arityChoices(s: SearchState, bounds: Map<Int, Int>): Sequence<Map<Int, Int>> {
        val committed = s.labelArities.filterKeys { it in s.committedLabels }
        val (labels, maxes) = bounds.mapValues { it.value + extraArities }.toList().unzip()
        if (maxes.any { it < 0 }) return emptySequence()
        // lazyCartesianProduct has no choices, not one empty choice, for no labels
        val choices =
            if (labels.isEmpty()) sequenceOf(emptyList())
            else lazyCartesianProduct(maxes.map { (0..it).toList() })
        return choices.map { committed + labels.zip(it) }
    }

    /**
     * For each of [withLabelClasses], the most parameters each of its labels that isn't committed may
     * need, as the solver bounds it. A label the solver doesn't bound may need none. For an outline
     * the solver finds unsatisfiable, every bound is -1. [merged] is whether they are
     * [mergedOutlines].
     */
    private fun solvedArityBounds(
        withLabelClasses: Set<SearchState>,
        merged: Boolean,
    ): List<Pair<SearchState, Map<Int, Int>>> =
        Stats.phase(statsId, Phase.ARITY) {
            // First the dependency analyses, one at a time, memoized by arities
            val dependencyAnalyses = mutableMapOf<Map<String, Int>, ParameterwiseDependencyAnalysis>()
            val seedsWithDeps =
                withLabelClasses.map { s ->
                    val arities = s.fnArities()
                    val dep =
                        dependencyAnalyses.getOrPut(arities) {
                            ParameterwiseDependencyAnalysis(
                                examples,
                                arities,
                                oracle,
                                config.resultDependence,
                                names = s.names.filterValues { it >= s.numCommittedTypes }.keys
                            )
                        }
                    s to dep
                }

            // Then the labelArities() calls, in parallel
            val bounds =
                seedsWithDeps
                    .parallelStream()
                    .map { (s, dep) -> s to labelArities(s, dep) }
                    .collect(Collectors.toList())
            val unsat = bounds.count { it.second == null }.toLong()
            Stats.add(Count.ARITY_UNSAT, unsat)
            if (merged) Stats.add(Count.MERGES_ARITY_UNSAT, unsat)

            bounds.map { (s, la) ->
                // The solver leaves committed labels out, so they keep their arities
                require(la == null || la.keys.none { it in s.committedLabels })
                s to uncommittedLabels(s).associateWith { if (la == null) -1 else la[it] ?: 0 }
            }
        }

    /**
     * Each outline with every choice of arities from 0 to [bound] for its labels. Committed labels
     * keep their arities, as do labels no type mentions.
     */
    private fun deepenLabelArities(outlines: Set<SearchState>, bound: Int): Map<SearchState, List<SearchState>> =
        withArities(outlines.flatMap { s ->
            val labels = uncommittedLabels(s).toList()
            val kept = s.labelArities.filterKeys { it !in labels }
            // lazyCartesianProduct has no choices, not one empty choice, for no labels
            val choices =
                if (labels.isEmpty()) sequenceOf(emptyList())
                else lazyCartesianProduct(labels.map { (0..bound).toList() })
            choices.map { s to kept + labels.zip(it) }
        })

    /** [choices] of arities for outlines as seeds, by outline. */
    private fun withArities(choices: List<Pair<SearchState, Map<Int, Int>>>): Map<SearchState, List<SearchState>> {
        val seeds =
            choices.groupBy({ it.first }) { (s, subla) -> s.mapTypesAndSetLabelArities(subla) { it.addParamHoles(subla) } }
        Stats.add(Count.SEEDS, seeds.values.sumOf { it.size }.toLong())
        return seeds
    }

    /** Passes the clashes it finds to [onClash]. */
    private fun concretizationSearch(
        seeds: List<SearchState>,
        currentSizeBound: Int,
        currentDepthBound: Int,
        onClash: (Set<Int>) -> Unit,
    ): Sequence<SearchState> {
        // Things blow up here, so sequencing
        // We start by searching for the functions, and try to deduce the nullaries from them.
        val candidatesNullariesDeduced =
            seeds.asSequence().flatMap {
                allCandidates(
                    it,
                    emitLabelBlanks = false,
                    emitConstructors = true,
                    sizeBound = currentSizeBound,
                    depthBound = currentDepthBound,
                    onClash = onClash,
                )
            }

        // If the functions are not contradictory but we couldn't deduce the nullaries, we transform
        // blanks into normal holes and enumerate for them
        val finalResults =
            candidatesNullariesDeduced.flatMap {
                if (it.noHoles()) sequenceOf(it)
                // We only want to enumerate the nullaries. If there are still holes under function
                // types, we simply didn't have the size or depth budget to finish. jk. this logic
                // is directly handled in dfs enumerator
                //                else if (it.types.filterIsInstance<Arrow>().all { it.noHoles() })
                else {
                    val blanksReplacedWithHoles =
                        it.mapTypes { t ->
                            t.blanks().fold(t) { acc: Type, h: THole ->
                                if (h is Blank) acc.replace(h, TypeHole()) else acc
                            }
                        }
                    // Need to respect depth bound here or in conservative FF
                    allCandidates(
                        blanksReplacedWithHoles,
                        emitLabelBlanks = false,
                        emitConstructors = true, // TODO false loses completeness and is especially broken with no union ff
                        sizeBound = currentSizeBound,
                        depthBound = currentDepthBound,
                        onClash = onClash,
                    )
                } // else emptySequence()
            }.filter { s ->
                examples.neg.all { !OneUnification(s, listOf(it)).ok }
                    .also { if (!it) Stats.inc(Count.PRUNED_NEG_FINAL) }
            }
        return finalResults
    }

    /**
     * Charges its work to concretizing, except for the parts that are outlining and solving for
     * label arities.
     */
    fun solutions(): Sequence<SearchState> = sequence {
        // Each larger seed depth, depth and size bound finds the solutions of the smaller ones again.
        // Yielding one twice would make the next round search for it twice.
        val yielded = mutableListOf<SearchState>()
        for (seedDepth in 0..config.depthBound) {
            var outlines = outlines(seedDepth)
            // Every outline of this seed depth so far, merged or not
            val seen = outlines.toHashSet()
            var merged = false
            while (outlines.isNotEmpty()) {
                val clashes = LinkedHashMap<SearchState, MutableSet<Set<Int>>>()
                yieldAll(concretize(seeds(outlines, merged), seedDepth, merged, clashes, yielded))
                outlines = mergedOutlines(clashes, seen)
                merged = true
            }
        }
    }.inPhase(statsId, Phase.CONCRETIZE)

    /**
     * The solutions of [seeds] that aren't in [yielded], to which it adds them. Adds the clashes
     * of each outline's seeds to [clashes]. [merged] is whether the outlines are [mergedOutlines].
     */
    private fun concretize(
        seeds: Map<SearchState, List<SearchState>>,
        seedDepth: Int,
        merged: Boolean,
        clashes: MutableMap<SearchState, MutableSet<Set<Int>>>,
        yielded: MutableList<SearchState>,
    ): Sequence<SearchState> = sequence {
        if (seeds.isEmpty()) return@sequence
        Debug.log { seeds.values.flatten().countedLines("Concrete seeds") }

        val maxMinSize = seeds.values.maxOf { outlineSeeds -> outlineSeeds.maxOf { it.numFillableHoles() } }
        Debug.log { "Max min size: $maxMinSize" }
        if (maxMinSize > config.sizeBound)
            Debug.log { "Warning: the largest seed contains more holes than the size bound" }

        for (depth in 1..config.depthBound) {
            // If largest seed is greater than the size bound, just try size bound for smaller seeds
            for (size in maxMinSize.coerceAtMost(config.sizeBound)..config.sizeBound) {
                for ((outline, outlineSeeds) in seeds) {
                    val outlineClashes = clashes.getOrPut(outline) { LinkedHashSet() }
                    val onClash: (Set<Int>) -> Unit = {
                        recordedClashes.add(it)
                        outlineClashes.add(it)
                    }
                    for (solution in concretizationSearch(outlineSeeds, size, depth, onClash)) {
                        if (yielded.any { it.equivalentTo(solution) }) continue
                        yielded.add(solution)
                        Stats.inc(Count.SOLUTIONS)
                        if (merged) Stats.inc(Count.MERGED_SOLUTIONS)
                        Stats.event(
                            "solution",
                            mapOf(
                                "seedDepth" to seedDepth,
                                "depth" to depth,
                                "size" to size,
                                // The types this search found, not those it was given
                                "types" to
                                    solution.names.filterValues { seed.types[it].allHoles().isNotEmpty() }
                                        .mapValues { (_, i) -> solution.types[i].toString() }
                            )
                        )
                        yield(solution)
                    }
                }
            }
        }
    }

    private fun Type.addParamHoles(labelArities: Map<Int, Int>, underArrow: Boolean = false): Type =
        when (this) {
            is Arrow ->
                Arrow(
                    l.addParamHoles(labelArities, underArrow = true),
                    r.addParamHoles(labelArities, underArrow = true)
                )
            is NamedLabel -> {
                // Only a label that was a blank has fewer parameters than its arity: none
                val arity = labelArities[this.label] ?: 0
                if (this.params.size != arity) {
                    // Children of labels are type holes if under a function, and blanks with
                    // labelOnly=false if under a nullary
                    this.copy(
                        params =
                        List(arity) {
                            if (underArrow) TypeHole() else Blank(labelOnly = false)
                        })
                } else this.copy(
                    params = params.map { it.addParamHoles(labelArities, underArrow) })
            }
            is THole,
            is Variable -> this
        }
}
