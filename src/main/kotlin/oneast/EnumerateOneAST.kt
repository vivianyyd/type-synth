package oneast

import dependencyanalysis.ParameterwiseDependencyAnalysis
import query.Name
import query.Query
import util.Counter
import util.IntUnionFind
import util.Logger
import util.Oracle

/** Fills one hole at a time, in DFS priority order. */
class EnumerateOneAST(
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
        allowBlanks: Boolean,
        sizeBound: Int
    ): Sequence<SearchState> {
        if (c.noHoles()) return sequenceOf(c)
        // TODO consider if I want to fast forward here, or do it later outside this fn
        //   call. Fast forwarding won't do anything in the first round when we purposefully
        //   have blanks since no labels yet, and in fact, it is probably actually bad!
        //   on the other hand, in the future iterations, we may as well fast forward outside
        //   this function. And in that case, we can combine this line with the c.noHoles()
        //   check.
        if (c.noFillableHoles()) return sequenceOf(c)

        if (sizeBound == 0) {
            val ff = fastForward(c)
            return if (ff.noHoles()) sequenceOf(ff) else sequenceOf()
        }

        val (iToFill, holeWithDepth) =
            c.types.mapNotNull { it.shallowestFillableHole() }.withIndex().minBy { it.value.second }
        val (hole, depth) = holeWithDepth

        return hole
            .expansions(
                unification = unification,
                labelArities = c.labelArities,
                vars = c.types[iToFill].variables().size,
                allowBlanks = allowBlanks,
                mustBeLeaf = sizeBound <= 1 || depth > hardDepthBound
            )
            .asSequence()
            .map {
                SearchState(
                    c.names,
                    c.types.mapIndexed { i, p -> if (iToFill == i) p.replace(hole, it) else p })
            }
            .flatMap { newCandidate ->
                logger.count("Total candidates for $seed")
                // todo the below check is commented out bc the mustBeLeaf flag includes depth now,
                //  check if that works
                // if (newCand.maxParamHeight() > hardDepthBound) emptySequence()
                val u = posUnification(newCandidate)
                if (u.ok()) commit(newCandidate, u, allowBlanks, sizeBound - 1) else emptySequence()
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
        s.names.zip(s.types).forEachIndexed { i, (n1, t1) ->
            s.names.zip(s.types).forEachIndexed { j, (n2, t2) ->
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

        return SearchState(s.names, s.types.map { assignLabels(it) })
    }

    fun enumerate(): List<SearchState> {
        fun check(c: SearchState) =
            posUnification(c).ok() && query.neg.all { !OneUnification(c, listOf(it)).ok() }

        val seed = SearchState(query.names, query.names.map { TypeHole() })
        val firstRound =
            commit(seed, posUnification(seed), allowBlanks = true, hardSizeBound).toList()

        val withLabelClasses = firstRound.mapNotNull { assignLabelClasses(it) }

        val dependencyAnalyses = mutableMapOf<Map<String, Int>, ParameterwiseDependencyAnalysis>()
        val solveLabels = withLabelClasses.map {
            val arities = it.fnArities()
            val dep =
                dependencyAnalyses.getOrPut(arities) {
                    ParameterwiseDependencyAnalysis(query, arities, oracle)
                }

            TODO(
                "We have to allow ourselves to return things with blanks, so that we" +
                        "can access constraints on them here"
            )

            TODO(
                "Turn all Blanks into Labels to solve for. " +
                        "Dependency analysis, then find label classes, then label arity constraints" +
                        "When generating named label nodes, give them type holes unless it's in a nullary, " +
                        "in which case give them Blanks where labelOnly=false"
            )
            }

        val secondRounds =
            solveLabels.flatMap {
                commit(it, posUnification(it), allowBlanks = false, hardSizeBound)
            }

        val finalResults =
            secondRounds.flatMap {
                commit(
                    TODO("[it] with blanks replaced with normal holes again"),
                    posUnification(it),
                    allowBlanks = false,
                    hardSizeBound
                )
            }
        TODO(
            "Once we have exhausted the search space for non-nullaries / found solutions, at that point" +
                    "we transform blanks back into normal holes and enumerate for them"
        )

        val blanknullaryseed =
            SearchState( // infer nullaries
                seed.names,
                seed.types.map { t ->
                    val commits: List<Pair<Hole, Blank>> =
                        when (t) {
                            is NArrow<*> -> listOf()
                            else -> t.listHoles().map { it to (it as ConcreteHole).blankExpansion }
                        }
                    commits.fold(t) { acc: SearchNode, commitment: Pair<Hole, Blank> ->
                        acc.replace(
                            commitment.first,
                            commitment.second as SearchNode) // TODO Extremely messy
                    }
                })
        // TODO bug: inferring nullaries can fail if there are multiple possible assignments of
        // variables to a nullary
        //      value. fix this later, solution is in notes
        return commit(seed, posUnification(this.seed), sizeBound, hardDepthBound)
            .filter { c -> check(c) }
            .toList()
    }

    fun fastForward(candidate: SearchState): SearchState {
        var curr = candidate
        do {
            val u = posUnification(curr)
            val commitments =
                curr.types.map { t ->
                    t.allHoles().map { it to it.fastForward(u, t.variables().size) }
                }
            curr =
                SearchState(
                    curr.names,
                    curr.types.zip(commitments).map { (t, commits) ->
                        commits.fold(t) { acc: Type, (hole, ty): Pair<THole, Type?> ->
                            if (ty == null) acc else acc.replace(hole, ty)
                        }
                    })
        } while (commitments.any { it.isNotEmpty() && it.any { it.second != null } })
        return curr
    }
}
