package oneast.searchstrategies

import oneast.Blank
import oneast.OneUnification
import oneast.SearchState
import oneast.SearchStrategy
import query.Examples
import util.Logger

/** Fills one hole at a time, shallowest first, in DFS style. */
class DFSEnumerator(examples: Examples) : SearchStrategy(examples) {
    // TODO can also implement a stateful version where we mutate the tree by picking a hole which
    //   has a parent pointer, for each of the expansions, modify the parent and recurse. when done,
    //   restore tree to original state
    override fun candidates(
        c: SearchState,
        unification: OneUnification,
        introduceBlanks: Boolean,
        fastForwardBlanks: Boolean,
        sizeBound: Int,
        depthBound: Int,
        loggingSeed: SearchState,
        logger: Logger
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

        if (sizeBound == 0) return emptySequence()

        val (iToFill, holeWithDepth) = c.shallowestFillableHole() ?: error("Impossible")
        val (hole, depth) = holeWithDepth
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
            .map { it to c.mapTypeAtIndex(iToFill) { typ -> typ.replace(hole, it) } }
            .filterNot { (_, newC) -> newC.types[iToFill].invalid() }
            .flatMap { (replacement, newCandidate) ->
                logger.count("Total candidates")
                val u = posUnification(newCandidate)
                if (u.ok()) {
                    // Committing a blank at the top-level is free
                    val cost =
                        if (replacement is Blank && newCandidate.types.any { it == replacement }) 0
                        else 1
                    candidates(
                        newCandidate,
                        u,
                        introduceBlanks,
                        fastForwardBlanks,
                        sizeBound - cost,
                        depthBound,
                        loggingSeed,
                        logger
                    )
                } else emptySequence()
            }
    }
}
