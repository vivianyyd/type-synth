package oneast.searchstrategies

import oneast.OneUnification
import oneast.SearchState
import query.Examples
import util.Logger

/** Fills one hole at a time, shallowest first, in DFS style. */
class DFSEnumerator(
    examples: Examples,
    private val emitLabelBlanks: Boolean,
    private val emitConstructors: Boolean,
    private val sizeBound: Int,
    private val depthBound: Int,
    private val logger: Logger
) : SearchStrategy(examples) {
    // TODO can also implement a stateful version where we mutate the tree by picking a hole which
    //   has a parent pointer, for each of the expansions, modify the parent and recurse. when done,
    //   restore tree to original state
    override fun candidates(c: SearchState): Sequence<SearchState> {
        val u = posUnification(c)
        return if (u.ok) recCandidates(c, u, sizeBound, c.types.sumOf { it.numFillableHoles() })
        else emptySequence()
    }

    /**
     * As long as seed [c] passes positive examples, states returned by this function do as well.
     */
    private fun recCandidates(
        c: SearchState,
        unification: OneUnification,
        currSizeBound: Int,
        holesRemaining: Int
    ): Sequence<SearchState> {
        if (c.noHoles()) return sequenceOf(c)

        // We won't fast-forward label blanks that we ourselves emitted.
        if (c.noFillableHoles())
            return if (!emitLabelBlanks) unionFastForward(c, depthBound)
            else sequenceOf(c)

        if (currSizeBound - holesRemaining < 0) return emptySequence()

        val (iToFill, hole, depth) = c.shallowestFillableHole() ?: error("Impossible")
        return hole
            .expansions(
                unification = unification,
                labelArities = c.labelArities,
                vars = c.types[iToFill].variables().size,
                canBeVar = hole != c.types[iToFill],
                emitLabelBlanks = emitLabelBlanks,
                emitConstructors = emitConstructors,
                mustBeLeaf = currSizeBound - holesRemaining <= 1 || depth >= depthBound
            )
            .asSequence()
            .map {
                logger.count("Total candidates")
                it.numFillableHoles() to c.mapTypeAtIndex(iToFill) { typ -> typ.replace(hole, it) }
            }
            .filterNot { (_, newCandidate) -> failsNegexWithNoHoleConstraints(newCandidate) }
            .flatMap { (introducedHoles, newCandidate) ->
                val u = posUnification(newCandidate)
                if (u.ok)
                    recCandidates(
                        newCandidate,
                        u,
                        currSizeBound = currSizeBound - 1,
                        holesRemaining = holesRemaining - 1 + introducedHoles
                    )
                else emptySequence()
            }
    }
}
