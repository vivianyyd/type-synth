package oneast

import dependencyanalysis.ParameterwiseDependencyAnalysis
import query.Examples
import util.*
import java.util.stream.Collectors
import java.util.stream.StreamSupport

/** Lazily produces ALL solutions for [examples] from this [seed]. */
class Search(
    private val seed: SearchState,
    private val examples: Examples,
    private val oracle: Oracle,
    private val config: Configuration,
    private val logger: Logger
) {
    private val names = seed.names.keys

    private fun allCandidates(
        c: SearchState,
        emitLabelBlanks: Boolean,
        emitConstructors: Boolean,
        sizeBound: Int,
        depthBound: Int,
    ): Sequence<SearchState> =
        config
            .searchStrategy(examples, emitLabelBlanks, emitConstructors, sizeBound, depthBound, logger)
            .candidates(c)

    private fun posUnification(s: SearchState) = OneUnification(s, examples.posNoSubexprs)

    /** Find all blanks, which must only be equal to other blanks, and assign them label classes. */
    private fun assignLabelClasses(s: SearchState): SearchState? {
        val u = posUnification(s)
        val uf = IntUnionFind()

        // Make equivalence classes of blanks
        s.blanks().forEach { blank ->
            u.holeEquals(blank).forEach { other ->
                if (other is InstantiationTy) {
                    if (other.hole !is Blank) return null
                    require(blank.labelOnly && other.hole.labelOnly)
                    uf.union(blank.id, other.hole.id)
                }
            }
        }

        // TODO It's not really clear why we need this if we've done the previous step properly but
        //   we do sooo that is bad. Do we still need it if all primitives of a single type are the
        //   same atom?
        // TODO actually we were indeed doing the previous step wrong... wasn't actually forcing the
        //   unification thunk so there were no hole constraints. See if we can remove this one now
        //        for ((n1, i) in s.names) {
        //            for ((n2, j) in s.names) {
        //                val t1 = s.types[i]
        //                val t2 = s.types[j]
        //                if (i < j && t1 is Blank && t2 is Blank && oracle.equal(Name(n1),
        // Name(n2)))
        //                    uf.union(t1.id, t2.id)
        //            }
        //        }

        // Set up mapping to assign labels to equivalence classes
        val freshLabel = Counter()
        freshLabel.ensureGt(s.labelArities.keys.maxOrNull() ?: -1)
        val holeToLabel = mutableMapOf<Int, Int>()

        // Populate with bindings to existing labels
        val holes = s.types.flatMap { it.allHoles() }.filterIsInstance<Blank>()
        holes.forEach {
            val constructors = u.holeEquals(it).filterIsInstance<ConstraintTypeConstructor>()
            if (constructors.isNotEmpty()) {
                if (constructors.any { !it.match(constructors.first()) || it is ConstraintArrow })
                    return null
                val label = (constructors.first() as ConstraintLabel).label
                val canonical = uf.find(it.id) ?: it.id
                if (canonical in holeToLabel && holeToLabel[canonical] != label) return null
                else if (canonical !in holeToLabel) holeToLabel[canonical] = label
            }
        }

        // Iterate through types and substitute labels for blanks - either the hole's equivalence
        // class' canonical element already has a label, or we make a fresh one
        fun getLabel(h: Blank) = holeToLabel.getOrPut(uf.find(h.id) ?: h.id) { freshLabel.get() }

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
        val initialOutlines =
            logger.time("Initial outlines") {
                allCandidates(
                    seed,
                    emitLabelBlanks = true,
                    emitConstructors = true,
                    sizeBound = size,
                    depthBound = depth,
                )
                    .filter { s ->
                        examples.neg.all { !OneUnification(s, listOf(it)).passedWithNoConstraints }
                    }
            }

        val withLabelClasses = initialOutlines.mapNotNull { assignLabelClasses(it) }.toSet()

        logger.log(withLabelClasses.countedLines("Seeds before label arities"))

        val seedsWithDeps =
            logger.time("Dependency analysis") {
                // Phase 1: compute dependency analyses sequentially (memoized by arities)
                val dependencyAnalyses =
                    mutableMapOf<Map<String, Int>, ParameterwiseDependencyAnalysis>()
                withLabelClasses.map { s ->
                    val arities = s.fnArities()
                    val dep =
                        dependencyAnalyses.getOrPut(arities) {
                            ParameterwiseDependencyAnalysis(examples, arities, oracle)
                        }
                    s to dep
                }
            }

        val resolvedLabelArities =
            logger.time("Solving for label arities") {
                // Phase 2: run labelArities() calls in parallel
                seedsWithDeps
                    .parallelStream()
                    .flatMap { (s, dep) ->
                        val la = labelArities(s, dep)
                        if (la == null) java.util.stream.Stream.empty()
                        else {
                            val (labels, arities) = la.toList().unzip()
                            StreamSupport.stream(
                                lazyCartesianProduct(arities.map { (0..it).toList() })
                                    .map { labels.zip(it).toMap() }
                                    .map { subla ->
                                        // TODO - if any of the new label arity assignments disagree
                                        //   w previous, we clear them
                                        s.mapTypesAndSetLabelArities(subla) {
                                            it.addParamHoles(subla)
                                        }
                                    }
                                    .asIterable()
                                    .spliterator(),
                                false)
                        }
                    }
                    .collect(Collectors.toList())
            }
        return resolvedLabelArities
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
                logger.count("Seeds")
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
        // TODO completeness bug here: Our fast forward is too aggressive; if we successfully fast
        // forward but to something that doesn't actually work, we miss all other candidates with
        // the same fn signatures but different nullaries.
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
                        emitConstructors = false, // TODO here is something we are testing out.
                        sizeBound = currentSizeBound,
                        depthBound = currentDepthBound,
                    )
                } // else emptySequence()
            }

        return finalResults.filter { c ->
            if (!(posUnification(c).ok))
                error(
                    "Enumerator should never return something that fails posexs at concretization stage"
                )
            examples.neg.all { !OneUnification(c, listOf(it)).ok }
        }
    }

    private fun <T> ifFirst(seq: Sequence<T>, condition: (T) -> Boolean): Sequence<T> {
        val iterator = seq.iterator()

        return if (!iterator.hasNext()) {
            emptySequence()
        } else {
            val first = iterator.next()

            if (condition(first)) {
                sequence {
                    yield(first)
                    yieldAll(iterator)
                }
            } else {
                emptySequence()
            }
        }
    }

    fun solutions(): Sequence<SearchState> = sequence {
        val seen = mutableSetOf<SearchState>()
        for (seedDepth in 0..config.depthBound) {
            var seeds =
                logger.time("Depth $seedDepth outlining $names") {
                    concreteSeeds(config.sizeBound, seedDepth)
                }
            // Only try concretizing the new seeds
            seeds = (seeds.toSet() - seen).toList()
            seen.addAll(seeds)

            if (seeds.isEmpty()) continue
            logger.log(seeds.countedLines("Concrete seeds"))

            val maxMinSize = seeds.maxOf { it.numFillableHoles() }
            logger.log("Max min size: $maxMinSize")

            for (depth in 1..config.depthBound) {
                logger.start("Depth $depth concretizing $names")
                for (size in maxMinSize..config.sizeBound) {
                    logger.start("Size $size concretizing $names")
                    val sols = concretizationSearch(seeds, size, depth).iterator()
                    yieldAll(sols)
                    logger.stop("Size $size concretizing $names")
                }
                logger.stop("Depth $depth concretizing $names")
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
