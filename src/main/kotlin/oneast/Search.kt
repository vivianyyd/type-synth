package oneast

import dependencyanalysis.ParameterwiseDependencyAnalysis
import query.Examples
import util.*
import java.util.stream.Collectors

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
        val holes = s.types.flatMap { it.allHoles() }
        val blanks = holes.filterIsInstance<Blank>()
        // An outline has no type holes left. If one is here, a blank it was unified with could still
        // turn into anything, so nothing can be concluded about that blank's label.
        if (blanks.size != holes.size) return null
        require(blanks.all { it.labelOnly })

        // Make equivalence classes of blanks: in each class, tie every blank to the first blank
        // seen there. A blank instantiated in two classes takes part in both ties, so blanks that
        // are connected only through it end up in one class as well.
        val firstBlankInClass = HashMap<Int, Int>()
        blanks.forEach { blank ->
            for (cls in u.classesOf(blank)) {
                val first = firstBlankInClass.putIfAbsent(cls, blank.id)
                if (first != null) uf.union(blank.id, first)
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
        blanks.forEach {
            val label =
                when (val constructor = u.holeConstructor(it)) {
                    HoleConstructor.None -> return@forEach
                    HoleConstructor.Conflicting, HoleConstructor.Arrow -> return null
                    is HoleConstructor.Label -> constructor.label
                }
            val canonical = uf.find(it.id) ?: it.id
            if (canonical in holeToLabel && holeToLabel[canonical] != label) return null
            else if (canonical !in holeToLabel) holeToLabel[canonical] = label
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

        val labelAritySols =
            logger.time("Solving for label arities") {
                // Phase 2: run labelArities() calls in parallel
                seedsWithDeps
                    .parallelStream()
                    .map { (s, dep) ->
                        logger.count("Solver call")
                        val la = labelArities(s, dep)
                        s to la
                    }
                    .filter { (_, la) -> la != null }
                    .collect(Collectors.toList())
            }

        val splitLabelArities = labelAritySols
            .flatMap { (s, la) ->
                require(la!!.all { (l, a) -> if (l in s.committedLabels) a == s.labelArities[l] else true })
                val (labels, arities) = la.toList().unzip()
                lazyCartesianProduct(arities.map { (0..it).toList() })
                    .map { s to labels.zip(it).toMap() }
            }
            // Order seeds by whether label arities from previous rounds are preserved
            .partition { (s, subla) -> s.labelArities.all { (l, a) -> subla[l] == a } }
            .let { it.first + it.second }

        val resolvedLabelArities =
            splitLabelArities.map { (s, subla) -> // New label arities overwrite old ones
                s.mapTypesAndSetLabelArities(subla) { t ->
                    t.addParamHoles(subla)
                }
            }

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
            }
        return finalResults
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
//        val seen = mutableSetOf<SearchState>()
        for (seedDepth in 0..config.depthBound) {
            var seeds =
                logger.time("Depth $seedDepth outlining $names") {
                    concreteSeeds(config.sizeBound, seedDepth)
                }
            // Only try concretizing the new seeds
            // TODO this doesn't work right now since holes use physical equals!
//            seeds = (seeds.toSet() - seen).toList()
//            seen.addAll(seeds)

            if (seeds.isEmpty()) continue
            logger.log(seeds.countedLines("Concrete seeds"))

            val maxMinSize = seeds.maxOf { it.numFillableHoles() }
            logger.log("Max min size: $maxMinSize")
            if (maxMinSize > config.sizeBound)
                logger.log("Warning: the largest seed contains more holes than the size bound")

            for (depth in 1..config.depthBound) {
                logger.start("Depth $depth concretizing $names")
                // If largest seed is greater than the size bound, just try size bound for smaller seeds
                for (size in maxMinSize.coerceAtMost(config.sizeBound)..config.sizeBound) {
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
