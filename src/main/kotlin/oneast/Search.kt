package oneast

import dependencyanalysis.ParameterwiseDependencyAnalysis
import query.Examples
import query.Name
import util.*

abstract class SearchStrategy(private val examples: Examples) {
    abstract fun candidates(
        c: SearchState,
        unification: OneUnification,
        introduceBlanks: Boolean,
        fastForwardBlanks: Boolean,
        sizeBound: Int,
        depthBound: Int,
        loggingSeed: SearchState,
        logger: Logger
    ): Sequence<SearchState>

    protected fun posUnification(s: SearchState) = OneUnification(s, examples.posNoSubexprs)

    protected fun fastForward(candidate: SearchState): SearchState? {
        var curr = candidate
        do {
            var changed = false
            val u = posUnification(curr)
            curr =
                curr.mapTypes { t ->
                    val changes =
                        t.allHolesWithDepth(topLevel = true).map { (hole, depth) ->
                            hole to hole.fastForward(u, topLevel = depth == 0)
                        }
                    if (changes.isNotEmpty() && changes.any { it.second != null }) changed = true
                    changes.fold(t) { acc: Type, (hole, ty): Pair<THole, Type?> ->
                        if (ty == null) acc else acc.replace(hole, ty)
                    }
                }
        } while (changed)
        return if (curr.noHoles()) curr else null
    }
}

/** Lazily produces ALL solutions for [examples] from this [seed]. */
class Search(
    private val seed: SearchState,
    private val examples: Examples,
    private val oracle: Oracle,
    private val config: Configuration,
    private val searchStrategy: (Examples) -> SearchStrategy,
    private val logger: Logger,
) {
    private fun commit(
        c: SearchState,
        unification: OneUnification,
        introduceBlanks: Boolean,
        fastForwardBlanks: Boolean,
        sizeBound: Int,
        depthBound: Int,
        loggingSeed: SearchState,
    ): Sequence<SearchState> =
        searchStrategy(examples)
            .candidates(
                c,
                unification,
                introduceBlanks,
                fastForwardBlanks,
                sizeBound,
                depthBound,
                loggingSeed,
                logger
            )

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

    private fun initialOutlines(callSolver: Boolean): List<SearchState> {
        val firstRound =
            logger.time("Initial search without labels or nullaries") {
                commit(
                    seed,
                    posUnification(seed),
                    introduceBlanks = true,
                    fastForwardBlanks = false,
                    sizeBound = Int.MAX_VALUE,
                    depthBound = Int.MAX_VALUE,
                    loggingSeed = seed
                )
                    .toList()
            }

        val withLabelClasses = firstRound.mapNotNull { assignLabelClasses(it) }

        logger.log(
            "Seeds before label arities: ${withLabelClasses.size}\n${withLabelClasses.lines()}"
        )

        val resolvedLabelArities =
            logger.time("Dependency analysis and solving for label arities") {
                val dependencyAnalyses =
                    mutableMapOf<Map<String, Int>, ParameterwiseDependencyAnalysis>()

                withLabelClasses.flatMap { s ->
                    val arities = s.fnArities()
                    val dep =
                        dependencyAnalyses.getOrPut(arities) {
                            ParameterwiseDependencyAnalysis(examples, arities, oracle)
                        }

                    val la = labelArities(s, dep, callSolver)
                    if (la == null) listOf()
                    else {
                        lazyCartesianProduct(la.values.map { (0..it).toList() })
                            .map { la.keys.zip(it).toMap() }
                            .map { s.mapTypesAndSetLabelArities(la) { it.addParamHoles(la) } }
                            .toList()
                    }
                }
            }
        return resolvedLabelArities.filter { it.types.all { !it.invalid() } }
    }

    private fun enumerate(
        seedOutlines: List<SearchState>,
        currentSizeBound: Int,
        currentDepthBound: Int,
    ): Sequence<SearchState> {
        fun check(c: SearchState) =
            posUnification(c).ok() && examples.neg.all { !OneUnification(c, listOf(it)).ok() }

        // Things blow up here, so sequencing
        val secondRounds =
            seedOutlines.asSequence().flatMap {
                commit(
                    it,
                    posUnification(it),
                    introduceBlanks = false,
                    fastForwardBlanks = true,
                    sizeBound = currentSizeBound,
                    depthBound = currentDepthBound,
                    loggingSeed = it
                )
            }

        // Once we have exhausted the search space for functions, we transform blanks back into
        // normal holes and enumerate for them
        val finalResults =
            secondRounds.flatMap {
                if (it.blanks().isEmpty()) sequenceOf(it)
                else {
                    val blanksReplacedWithHoles =
                        it.mapTypes { t ->
                            t.blanks().fold(t) { acc: Type, h: THole ->
                                if (h is Blank) acc.replace(h, TypeHole()) else acc
                            }
                        }
                    commit(
                        blanksReplacedWithHoles,
                        posUnification(blanksReplacedWithHoles),
                        introduceBlanks = false,
                        fastForwardBlanks = true,
                        sizeBound = currentSizeBound,
                        depthBound = currentDepthBound,
                        loggingSeed = blanksReplacedWithHoles
                    )
                }
            }

        return finalResults.filter { c -> check(c) }
    }

    fun solutions(): Sequence<SearchState> = sequence {
        val seedOutlines = initialOutlines(callSolver = true)
        logger.log("Concrete seeds: ${seedOutlines.size}\n${seedOutlines.lines()}")

        var solved = false
        for (depth in 1..config.depthBound) {
            logger.start("Depth $depth for ${examples.names}")
            for (size in 1..config.sizeBound) {
                logger.start("Size $size for ${examples.names}")
                val sols =
                    enumerate(
                        seedOutlines,
                        currentSizeBound = size,
                        currentDepthBound = depth,
                        // get all solutions to subproblems in case one partial solution is
                        // unrealizable
                    )
                        .iterator()
                if (sols.hasNext()) solved = true
                yieldAll(sols)
                logger.stop("Size $size for ${examples.names}")
                if (solved) {
                    logger.log("STOPPED AT SIZE $size")
                    break
                }
            }
            logger.stop("Depth $depth for ${examples.names}")
            if (solved) {
                logger.log("STOPPED AT DEPTH $depth")
                break
            }
        }
    }
}

fun Type.addParamHoles(labelArities: Map<Int, Int>, underArrow: Boolean = false): Type =
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
