package oneast

import dependencyanalysis.ParameterwiseDependencyAnalysis
import query.Name
import query.Query
import util.*

/** Fills one hole at a time, shallowest first, in DFS style. */
class EnumerateOneAST(
    val seed: SearchState,
    val query: Query,
    val oracle: Oracle,
    val config: Configuration,
    private val logger: Logger,
) {
    private fun posUnification(s: SearchState) = OneUnification(s, query.posNoSubexprs)

    // TODO can also implement a stateful version where we mutate the tree by picking a hole which
    //   has a parent pointer, for each of the expansions, modify the parent and recurse. when done,
    //   restore tree to original state
    private fun commit(
        c: SearchState,
        unification: OneUnification,
        introduceBlanks: Boolean,
        fastForwardBlanks: Boolean,
        sizeBound: Int,
        depthBound: Int,
        loggingSeed: SearchState,
    ): Sequence<SearchState> {
        if (c.noHoles()) return sequenceOf(c)
        // TODO consider if I want to fast forward here, or do it later outside this fn
        //   call. Fast forwarding won't do anything in the first round when we purposefully
        //   have blanks since no labels yet, and in fact, it is probably actually bad!
        //   on the other hand, in the future iterations, we may as well fast forward outside
        //   this function. And in that case, we can combine this line with the c.noHoles()
        //   check.

        fun fastForward(): Sequence<SearchState> {
            val ff = fastForward(c)
            return listOfNotNull(ff).asSequence()
        }

        if (c.noFillableHoles()) {
            return if (fastForwardBlanks) fastForward() else sequenceOf(c)
        }

        if (sizeBound == 0) return fastForward()

        val (iToFill, holeWithDepth) =
            c.types
                .withIndex()
                .map { it.index to it.value.shallowestFillableHole(topLevel = true) }
                .filter { it.second != null }
                .minBy { it.second!!.second }
        val (hole, depth) = holeWithDepth!!
        return hole
            .expansions(
                unification = unification,
                labelArities = c.labelArities,
                vars = c.types[iToFill].variables().size,
                topLevel = hole == c.types[iToFill],
                introduceBlanks = introduceBlanks,
                mustBeLeaf = sizeBound <= 1 || depth >= depthBound
            )
            .asSequence()
            .map {
                it to c.mapTypesIndexed { i, p -> if (iToFill == i) p.replace(hole, it) else p }
            }
            .flatMap { (replacement, newCandidate) ->
                logger.count("Total candidates")
                val u = posUnification(newCandidate)
                if (u.ok()) {
                    // Committing a blank at the top-level is free
                    val cost =
                        if (replacement is Blank && newCandidate.types.any { it == replacement }) 0
                        else 1
                    commit(
                        newCandidate,
                        u,
                        introduceBlanks,
                        fastForwardBlanks,
                        sizeBound - cost,
                        depthBound,
                        loggingSeed
                    )
                } else emptySequence()
            }
    }

    /** Find all blanks, which must only be equal to other blanks, and assign them label classes. */
    private fun assignLabelClasses(s: SearchState): SearchState? {
        val u = posUnification(s)
        val uf = IntUnionFind()

        s.blanks().forEach { blank ->
            u.holeEquals(blank).forEach { other ->
                if (other !is InstantiationTy || other.hole !is Blank) return null
                uf.union(blank.id, other.hole.id)
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
                            ParameterwiseDependencyAnalysis(query, arities, oracle)
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
        return resolvedLabelArities
    }

    private fun enumerate(
        seedOutlines: List<SearchState>,
        currentSizeBound: Int,
        currentDepthBound: Int,
        numSols: Solutions
    ): Sequence<SearchState> {
        fun check(c: SearchState) =
            posUnification(c).ok() && query.neg.all { !OneUnification(c, listOf(it)).ok() }

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

        return when (numSols) {
            Solutions.ALL_SOLUTIONS -> finalResults.filter { c -> check(c) }
            Solutions.ONE_SOLUTION -> sequenceOf(finalResults.first { c -> check(c) })
        }
    }

    private fun fastForward(candidate: SearchState): SearchState? {
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

    fun solutions(): Sequence<SearchState> = sequence {
        val seedOutlines = initialOutlines(callSolver = true)
        logger.log("Concrete seeds: ${seedOutlines.size}\n${seedOutlines.lines()}")

        var solved = false
        for (depth in 1..config.depthBound) {
            logger.start("Depth $depth for ${query.names}")
            for (size in 1..config.sizeBound) {
                logger.start("Size $size for ${query.names}")
                val sols =
                    enumerate(
                        seedOutlines,
                        currentSizeBound = size,
                        currentDepthBound = depth,
                        numSols = Solutions.ALL_SOLUTIONS
                        // get all solutions to subproblems in case one partial solution is
                        // unrealizable
                    )
                        .iterator()
                if (sols.hasNext()) solved = true
                yieldAll(sols)
                logger.stop("Size $size for ${query.names}")
                if (solved) {
                    logger.log("STOPPED AT SIZE $size")
                    break
                }
            }
            logger.stop("Depth $depth for ${query.names}")
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

enum class Solutions {
    ALL_SOLUTIONS,
    ONE_SOLUTION
}
