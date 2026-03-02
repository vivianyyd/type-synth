package oneast

import dependencyanalysis.ParameterwiseDependencyAnalysis
import oneast.searchstrategies.SearchStrategy
import query.Examples
import query.Name
import util.*
import java.util.Spliterator
import java.util.Spliterators
import java.util.stream.Collectors
import java.util.stream.Stream
import java.util.stream.StreamSupport

/** Lazily produces ALL solutions for [examples] from this [seed]. */
class Search(
    private val seed: SearchState,
    private val examples: Examples,
    private val oracle: Oracle,
    private val config: Configuration,
    // Using factory design pattern feels like giving up
    private val searchStrategy: (Examples, Boolean, Int, Int, Logger) -> SearchStrategy,
    private val logger: Logger,
) {
    private fun allCandidates(
        c: SearchState,
        emitLabelBlanks: Boolean,
        sizeBound: Int,
        depthBound: Int,
    ): Sequence<SearchState> =
        searchStrategy(examples, emitLabelBlanks, sizeBound, depthBound, logger)
            .candidates(c)

    private fun posUnification(s: SearchState) = OneUnification(s, examples.posNoSubexprs)

    /** Find all blanks, which must only be equal to other blanks, and assign them label classes. */
    private fun assignLabelClasses(s: SearchState): SearchState? {
        val u = posUnification(s)
        val uf = IntUnionFind()

        s.blanks().forEach { blank ->
            u.holeEquals(blank).forEach { other ->
                if (other is InstantiationTy) {
                    if (other.hole !is Blank) return null
                    uf.union(blank.id, other.hole.id)
                }
            }
        }

        // TODO It's not really clear why we need this if we've done the previous step properly but
        //   we do sooo that is bad
        for ((n1, i) in s.names) {
            for ((n2, j) in s.names) {
                val t1 = s.types[i]
                val t2 = s.types[j]
                if (i < j && t1 is Blank && t2 is Blank && oracle.equal(Name(n1), Name(n2)))
                    uf.union(t1.id, t2.id)
            }
        }

        val freshLabel = Counter()
        freshLabel.ensureGt(s.labelArities.keys.maxOrNull() ?: -1)
        val holeToLabel = mutableMapOf<Int, Int>()

        // Populate with equivalences to existing labels
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

        fun getLabel(h: Blank) = holeToLabel.getOrPut(uf.find(h.id) ?: h.id) { freshLabel.get() }

        fun assignLabels(t: Type): Type =
            when (t) {
                is Arrow -> Arrow(assignLabels(t.l), assignLabels(t.r))
                is NamedLabel -> t.copy(params = t.params.map { assignLabels(it) })
                is Blank ->
                    NamedLabel(
                        label = getLabel(t),
                        params = emptyList()
                    ) // empty since we haven't decided arities yet
                is TypeHole -> error("Shouldn't happen")
                is Variable -> t
            }

        return s.mapTypesAndSetLabelArities(mapOf()) { assignLabels(it) }
    }

    private fun concreteSeeds(): List<SearchState> {
        val initialOutlines =
            logger.time("Initial outlines") {
                allCandidates(
                    seed,
                    emitLabelBlanks = true,
                    sizeBound = Int.MAX_VALUE,
                    depthBound = Int.MAX_VALUE,
                )
                    .toList()
            }

        val withLabelClasses = initialOutlines.mapNotNull { assignLabelClasses(it) }

        logger.log(withLabelClasses.countedLines("Seeds before label arities"))

        val resolvedLabelArities =
            logger.time("Dependency analysis and solving for label arities") {
                val dependencyAnalyses =
                    mutableMapOf<Map<String, Int>, ParameterwiseDependencyAnalysis>()

                // Compute dependency analyses sequentially before launching parallel label solving.
                val statesWithDeps =
                    withLabelClasses.map { s ->
                        val arities = s.fnArities()
                        val dep =
                            dependencyAnalyses.getOrPut(arities) {
                                ParameterwiseDependencyAnalysis(examples, arities, oracle)
                            }
                        s to dep
                    }

                statesWithDeps
                    .parallelStream()
                    .flatMap { (s, dep) ->
                        val la = labelArities(s, dep)
                        if (la == null) Stream.empty()
                        else {
                            lazyCartesianProduct(la.values.map { (0..it).toList() })
                                .map { la.keys.zip(it).toMap() }
                                .map { s.mapTypesAndSetLabelArities(la) { it.addParamHoles(la) } }
                                .toStream()
                        }
                    }
                    .collect(Collectors.toList())
            }
        return resolvedLabelArities.filter { it.types.all { !it.invalid() } }
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
                if (it.blanks().isEmpty()) sequenceOf(it)
                else {
                    val blanksReplacedWithHoles =
                        it.mapTypes { t ->
                            t.blanks().fold(t) { acc: Type, h: THole ->
                                if (h is Blank) acc.replace(h, TypeHole()) else acc
                            }
                        }
                    allCandidates(
                        blanksReplacedWithHoles,
                        emitLabelBlanks = false,
                        sizeBound = currentSizeBound,
                        depthBound = currentDepthBound,
                    )
                }
            }

        return finalResults.filter { c ->
            posUnification(c).ok() && examples.neg.all { !OneUnification(c, listOf(it)).ok() }
        }
    }

    fun solutions(): Sequence<SearchState> = sequence {
        val seeds = concreteSeeds()
        logger.log(seeds.countedLines("Concrete seeds"))

        for (depth in 1..config.depthBound) {
            logger.start("Depth $depth for ${examples.names}")
            for (size in 1..config.sizeBound) {
                logger.start("Size $size for ${examples.names}")
                val sols =
                    concretizationSearch(
                        seeds,
                        currentSizeBound = size,
                        currentDepthBound = depth,
                    )
                        .iterator()
                yieldAll(sols)
                logger.stop("Size $size for ${examples.names}")
                // The contract is to provide *all* solutions, not just those of minimal size/depth
                // if (solved) break
            }
            logger.stop("Depth $depth for ${examples.names}")
            // if (solved) break
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
                // Only overwrite parameters if they are wrongly empty
                if ((labelArities[this.label] ?: 0) > 0 && this.params.isEmpty()) {
                    // Children of labels are type holes if under a function, and blanks with
                    // labelOnly=false if under a nullary
                    this.copy(
                        params =
                        List(labelArities[this.label]!!) {
                            if (underArrow) TypeHole() else Blank(labelOnly = false)
                        })
                } else this
            }
            is THole,
            is Variable -> this
        }
}

/** Converts a Kotlin [Sequence] to a sequential Java [Stream] while preserving order. */
private fun <T> Sequence<T>.toStream(): Stream<T> =
    StreamSupport.stream(
        Spliterators.spliteratorUnknownSize(iterator(), Spliterator.ORDERED),
        false
    )
