package oneast

import bench.*
import dependencyanalysis.ParameterwiseDependencyAnalysis
import query.Examples
import util.*
import java.util.stream.Collectors

/**
 * Lazily produces ALL solutions for [examples] from this [seed]. Charges its work to search
 * [statsId] (see [Stats.newSearch]).
 */
class Search(
    private val seed: SearchState,
    private val examples: Examples,
    private val oracle: Oracle,
    private val config: Configuration,
    private val statsId: Int = -1,
) {
    private fun allCandidates(
        c: SearchState,
        emitLabelBlanks: Boolean,
        emitConstructors: Boolean,
        sizeBound: Int,
        depthBound: Int,
    ): Sequence<SearchState> =
        config.searchStrategy
            .create(
                examples, emitLabelBlanks, emitConstructors, sizeBound, depthBound, config.soundExpansions
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
                // If it's a new label, we haven't decided its arity yet. If it's an existing label,
                // we could assign the appropriate arity here. But we will do it again later, and
                // the arity might be changed when we resolve anyway. So don't bother yet
                is TypeHole -> error("Shouldn't happen")
                is Variable -> t
            }

        return s.mapTypes { assignLabels(it) }
    }

    private fun concreteSeeds(size: Int, depth: Int): List<SearchState> {
        val withLabelClasses =
            Stats.phase(statsId, Phase.OUTLINE) {
                allCandidates(
                    seed,
                    emitLabelBlanks = true,
                    emitConstructors = true,
                    sizeBound = size,
                    depthBound = depth,
                )
                    .map {
                        Stats.inc(Count.OUTLINES)
                        assignLabelClasses(it)
                    }
                    .toSet()
            }

        Debug.log { withLabelClasses.countedLines("Seeds before label arities") }

        return Stats.phase(statsId, Phase.ARITY) {
            when (val la = config.labelArities) {
                LabelArities.Solved -> solveLabelArities(withLabelClasses)
                is LabelArities.Deepened -> deepenLabelArities(withLabelClasses, la.bound)
            }
        }
    }

    private fun solveLabelArities(withLabelClasses: Set<SearchState>): List<SearchState> {
        // First the dependency analyses, one at a time, memoized by arities
        val dependencyAnalyses = mutableMapOf<Map<String, Int>, ParameterwiseDependencyAnalysis>()
        val seedsWithDeps =
            withLabelClasses.map { s ->
                val arities = s.fnArities()
                val dep =
                    dependencyAnalyses.getOrPut(arities) {
                        ParameterwiseDependencyAnalysis(examples, arities, oracle)
                    }
                s to dep
            }

        // Then the labelArities() calls, in parallel
        val labelAritySols =
            seedsWithDeps
                .parallelStream()
                .map { (s, dep) -> s to labelArities(s, dep) }
                .filter { (_, la) -> la != null }
                .collect(Collectors.toList())
        Stats.add(Count.ARITY_UNSAT, (seedsWithDeps.size - labelAritySols.size).toLong())

        val resolvedLabelArities = withArities(labelAritySols
            .flatMap { (s, la) ->
                // The solver leaves committed labels out, so they keep their arities
                require(la!!.keys.none { it in s.committedLabels })
                val committed = s.labelArities.filterKeys { it in s.committedLabels }
                val (labels, arities) = la.toList().unzip()
                // lazyCartesianProduct has no choices, not one empty choice, for no labels
                val choices =
                    if (labels.isEmpty()) sequenceOf(emptyList())
                    else lazyCartesianProduct(arities.map { (0..it).toList() })
                choices.map { s to committed + labels.zip(it) }
            })

        // Without ordering seeds by arity preserved
//        val resolvedLabelArities = logger.time("Solving for label arities") {
//            seedsWithDeps.parallelStream().flatMap { (s, dep) ->
//                logger.count("Solver call")
//                val la = labelArities(s, dep)
//                if (la == null) java.util.stream.Stream.empty()
//                else {
//                    val (labels, arities) = la.toList().unzip()
//                    StreamSupport.stream(
//                        lazyCartesianProduct(arities.map { (0..it).toList() })
//                            .map {
//                                val subla = labels.zip(it).toMap()
//                                // New label arities overwrite old ones
//                                s.mapTypesAndSetLabelArities(subla) { t ->
//                                    t.addParamHoles(subla)
//                                }
//                            }.asIterable().spliterator(),
//                        false)
//                }
//            }.collect(Collectors.toList())
//        }

        return resolvedLabelArities
    }

    /**
     * Each outline with every choice of arities from 0 to [bound] for its labels. Committed labels
     * keep their arities, as do labels no type mentions.
     */
    private fun deepenLabelArities(outlines: Set<SearchState>, bound: Int): List<SearchState> =
        withArities(outlines.flatMap { s ->
            val labels = (s.types.flatMap { it.labels() }.map { it.first }.toSet() - s.committedLabels).toList()
            val kept = s.labelArities.filterKeys { it !in labels }
            // lazyCartesianProduct has no choices, not one empty choice, for no labels
            val choices =
                if (labels.isEmpty()) sequenceOf(emptyList())
                else lazyCartesianProduct(labels.map { (0..bound).toList() })
            choices.map { s to kept + labels.zip(it) }
        })

    /** [choices] of arities for outlines as seeds. */
    private fun withArities(choices: List<Pair<SearchState, Map<Int, Int>>>): List<SearchState> {
        val seeds = choices
            // Order seeds by whether label arities from previous rounds are preserved
            .partition { (s, subla) -> s.labelArities.all { (l, a) -> subla[l] == a } }
            .let { it.first + it.second }
            .map { (s, subla) -> // New label arities overwrite old ones
                s.mapTypesAndSetLabelArities(subla) { t ->
                    t.addParamHoles(subla)
                }
            }
        Stats.add(Count.SEEDS, seeds.size.toLong())
        return seeds
    }

    private fun concretizationSearch(
        seeds: List<SearchState>,
        currentSizeBound: Int,
        currentDepthBound: Int,
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
//        val seen = mutableSetOf<SearchState>()
        for (seedDepth in 0..config.depthBound) {
            var seeds = concreteSeeds(config.sizeBound, seedDepth)
            // Only try concretizing the new seeds
            // TODO this doesn't work right now since holes use physical equals!
//            seeds = (seeds.toSet() - seen).toList()
//            seen.addAll(seeds)

            if (seeds.isEmpty()) continue
            Debug.log { seeds.countedLines("Concrete seeds") }

            val maxMinSize = seeds.maxOf { it.numFillableHoles() }
            Debug.log { "Max min size: $maxMinSize" }
            if (maxMinSize > config.sizeBound)
                Debug.log { "Warning: the largest seed contains more holes than the size bound" }

            for (depth in 1..config.depthBound) {
                // If largest seed is greater than the size bound, just try size bound for smaller seeds
                for (size in maxMinSize.coerceAtMost(config.sizeBound)..config.sizeBound) {
                    for (solution in concretizationSearch(seeds, size, depth)) {
                        Stats.inc(Count.SOLUTIONS)
                        Stats.event(
                            "solution",
                            mapOf("seedDepth" to seedDepth, "depth" to depth, "size" to size)
                        )
                        yield(solution)
                    }
                }
            }
        }
    }.inPhase(statsId, Phase.CONCRETIZE)

    private fun Type.addParamHoles(labelArities: Map<Int, Int>, underArrow: Boolean = false): Type =
        when (this) {
            is Arrow ->
                Arrow(
                    l.addParamHoles(labelArities, underArrow = true),
                    r.addParamHoles(labelArities, underArrow = true)
                )
            is NamedLabel -> {
                // We *always* overwrite parameters if there is mismatch
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
