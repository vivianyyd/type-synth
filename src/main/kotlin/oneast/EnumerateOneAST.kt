package oneast

import dependencyanalysis.ParameterwiseDependencyAnalysis
import query.Name
import query.Query
import util.Counter
import util.IntUnionFind
import util.Logger
import util.Oracle

/** Fills one hole at a time, shallowest first, in DFS style. */
class EnumerateOneAST(
    val seed: SearchState,
    val query: Query,
    val oracle: Oracle,
    private val hardSizeBound: Int,
    private val hardDepthBound: Int,
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
        loggingSeed: SearchState,
    ): Sequence<SearchState> {
        if (c.noHoles()) return sequenceOf(c)
        // TODO consider if I want to fast forward here, or do it later outside this fn
        //   call. Fast forwarding won't do anything in the first round when we purposefully
        //   have blanks since no labels yet, and in fact, it is probably actually bad!
        //   on the other hand, in the future iterations, we may as well fast forward outside
        //   this function. And in that case, we can combine this line with the c.noHoles()
        //   check.
        if (c.noFillableHoles()) {
            return if (fastForwardBlanks) listOfNotNull(fastForward(c)).asSequence()
            else sequenceOf(c)
        }

        if (sizeBound == 0) return listOfNotNull(fastForward(c)).asSequence()

        val (iToFill, holeWithDepth) =
            c.types.mapNotNull { it.shallowestFillableHole() }.withIndex().minBy { it.value.second }
        val (hole, depth) = holeWithDepth

        return hole
            .expansions(
                unification = unification,
                labelArities = c.labelArities,
                vars = c.types[iToFill].variables().size,
                introduceBlanks = introduceBlanks,
                mustBeLeaf = sizeBound <= 1 || depth > hardDepthBound
            )
            .asSequence()
            .map { replacement -> c.updateTypeAt(iToFill, c.types[iToFill].replace(hole, replacement)) }
            .flatMap { newCandidate ->
                logger.count("Total candidates for $loggingSeed")
                // todo the below check is commented out bc the mustBeLeaf flag includes depth now,
                //  check if that works
                // if (newCand.maxParamHeight() > hardDepthBound) emptySequence()
                val u = posUnification(newCandidate)
                if (u.ok())
                    commit(
                        newCandidate,
                        u,
                        introduceBlanks,
                        fastForwardBlanks,
                        sizeBound - 1,
                        loggingSeed
                    )
                else emptySequence()
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

    fun enumerate(callSolver: Boolean, numSols: Solutions): List<SearchState> {
        fun check(c: SearchState) =
            posUnification(c).ok() && query.neg.all { !OneUnification(c, listOf(it)).ok() }

        val firstRound =
            commit(
                seed,
                posUnification(seed),
                introduceBlanks = true,
                fastForwardBlanks = false,
                hardSizeBound,
                loggingSeed = seed
            )
                .toList()

        val withLabelClasses = firstRound.mapNotNull { assignLabelClasses(it) }

        val dependencyAnalyses = mutableMapOf<Map<String, Int>, ParameterwiseDependencyAnalysis>()
        val resolvedLabelArities =
            withLabelClasses.mapNotNull { s ->
                val arities = s.fnArities()
                val dep =
                    dependencyAnalyses.getOrPut(arities) {
                        ParameterwiseDependencyAnalysis(query, arities, oracle)
                    }

                labelArities(s, dep, callSolver)?.let { la ->
                    s.mapTypesAndSetLabelArities(la) { it.addParamHoles(la) }
                }
            }

        // Things blow up here, so sequencing
        val secondRounds =
            resolvedLabelArities.asSequence().flatMap {
                commit(
                    it,
                    posUnification(it),
                    introduceBlanks = false,
                    fastForwardBlanks = true,
                    hardSizeBound,
                    it
                )
            }

        // Once we have exhausted the search space for functions, we transform blanks back into
        // normal holes and enumerate for them
        val finalResults =
            secondRounds.flatMap {
                val blanksReplacedWithHoles =
                    it.mapTypes { t ->
                        t.allHoles().fold(t) { acc: Type, h: THole ->
                            if (h is Blank) acc.replace(h, TypeHole()) else acc
                        }
                    }
                commit(
                    blanksReplacedWithHoles,
                    posUnification(blanksReplacedWithHoles),
                    introduceBlanks = false,
                    fastForwardBlanks = true,
                    hardSizeBound,
                    blanksReplacedWithHoles
                )
            }

        return when (numSols) {
            Solutions.ALL_SOLUTIONS -> finalResults.filter { c -> check(c) }.toList()
            Solutions.ONE_SOLUTION -> listOf(finalResults.first { c -> check(c) })
        }
    }

    fun fastForward(candidate: SearchState): SearchState? {
        var curr = candidate
        do {
            var changed = false
            val u = posUnification(curr)
            curr =
                curr.mapTypes { t ->
                    val changes = t.allHoles().map { it to it.fastForward(u) }
                    if (changes.isNotEmpty() && changes.any { it.second != null }) changed = true
                    changes.fold(t) { acc: Type, (hole, ty): Pair<THole, Type?> ->
                        if (ty == null) acc else acc.replace(hole, ty)
                    }
                }
        } while (changed)
        return if (curr.noHoles()) curr else null
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
