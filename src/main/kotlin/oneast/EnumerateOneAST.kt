package oneast

import query.Query
import util.Logger

/** Fills one hole at a time, in DFS priority order. */
class EnumerateOneAST(
    val query: Query,
    val seed: SearchState,
    private val mustPassNegatives: Boolean,
    private val logger: Logger,
) {
    // TODO can also implement a stateful version where we mutate the tree by picking a hole which
    //   has a parent pointer, for each of the expansions, modify the parent and recurse. when done,
    //   restore tree to original state
    /** The possible SearchStates resulting from filling one hole. */
    private fun fill(
        c: SearchState,
        unification: OneUnification,
        mustBeLeaf: Boolean
    ): Sequence<SearchState> {
        // todo can we remove bound on iterative deepening bc we fill shallowest hole first?
        val (iToFill, holeWithDepth) =
            c.types.mapNotNull { it.shallowestFillableHole() }.withIndex().minBy { it.value.second }
        val (hole, _) = holeWithDepth

        return hole
            .expansions(
                unification, seed.labelArities, c.types[iToFill].variables().size, mustBeLeaf)
            .asSequence()
            .map {
                SearchState(
                    c.names,
                    c.types.mapIndexed { i, p -> if (iToFill == i) p.replace(hole, it) else p })
            }
        // TODO merge this function with commitPriority so that if our commitment was a labelhole,
        // we don't reduce the size bound?
    }

    private fun commitPriority(
        c: SearchState,
        unification: OneUnification,
        sizeBound: Int,
        hardDepthBound: Int
    ): Sequence<SearchState> {
        if (c.noHoles()) return sequenceOf(c)

        if (sizeBound == 0 || c.noFillableHoles()) {
            val ff = fastForward(c)
            return if (ff.noHoles()) sequenceOf(ff) else sequenceOf()
        }

        return fill(c, unification, sizeBound <= 1).flatMap { newCand ->
            logger.count("Total candidates for $seed")
            if (newCand.maxParamHeight() > hardDepthBound) emptySequence()
            else {
                val u = OneUnification(newCand, query.posNoSubexprs)
                if (u.ok())
                    commitPriority(newCand, u, sizeBound - 1, hardDepthBound)
                else emptySequence()
            }
        }
    }

    fun enumerate(sketches: Boolean, sizeBound: Int, hardDepthBound: Int): List<SearchState> {
        fun check(c: SearchState) =
            OneUnification(c, query.posNoSubexprs).ok() &&
                (if (mustPassNegatives) query.neg.all { !OneUnification(c, listOf(it)).ok() }
                else true)

        val seed =
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
        return commitPriority(
                seed, OneUnification(this.seed, query.posNoSubexprs), sizeBound, hardDepthBound)
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
