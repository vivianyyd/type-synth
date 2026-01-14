package oneast

import query.Query
import util.Logger

/** Fills one hole at a time, in DFS priority order. */
class EnumerateOneAST(
    val query: Query,
    private val hardSizeBound: Int,
    private val hardDepthBound: Int,
    private val logger: Logger,
) {
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

        if (sizeBound == 0 || c.noFillableHoles()) {
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
                val u = OneUnification(newCandidate, query.posNoSubexprs)
                if (u.ok()) commit(newCandidate, u, allowBlanks, sizeBound - 1) else emptySequence()
            }
    }

    fun enumerate(): List<SearchState> {
        fun check(c: SearchState) =
            OneUnification(c, query.posNoSubexprs).ok() &&
                    (if (mustPassNegatives) query.neg.all { !OneUnification(c, listOf(it)).ok() }
                    else true)

        val seed = SearchState(query.names, query.names.map { TypeHole() })
        val firstRound =
            commit(
                seed, OneUnification(seed, query.posNoSubexprs), allowBlanks = true, hardSizeBound
            )

        TODO("Dependency analysis, then label arity constraints")

        val solveLabels =
            firstRound.map {
                TODO(
                    "Turn all Blanks into Labels to solve for. " +
                            "When generating named label nodes, give them type holes unless it's in a nullary, " +
                            "in which case give them Blanks where labelOnly=false"
                )
            }

        val secondRounds =
            solveLabels.flatMap {
                commit(
                    it, OneUnification(it, query.posNoSubexprs), allowBlanks = false, hardSizeBound
                )
            }

        val finalResults =
            secondRounds.flatMap {
                commit(
                    TODO("[it] with blanks replaced with normal holes again"),
                    OneUnification(it, query.posNoSubexprs),
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
        return commit(
            seed, OneUnification(this.seed, query.posNoSubexprs), sizeBound, hardDepthBound
        )
            .filter { c -> check(c) }
            .toList()
    }

    fun fastForward(candidate: SearchState): SearchState {
        var curr = candidate
        do {
            val u = OneUnification(curr, query.posNoSubexprs)
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
