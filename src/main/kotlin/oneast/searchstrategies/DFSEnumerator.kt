package oneast.searchstrategies

import oneast.OneUnification
import oneast.SearchState
import query.Examples
import util.Logger

/** Fills one hole at a time, shallowest first, in DFS style. */
class DFSEnumerator(
    examples: Examples,
    private val emitLabelBlanks: Boolean,
    private val sizeBound: Int,
    private val depthBound: Int,
    private val logger: Logger
) : SearchStrategy(examples) {
    // TODO can also implement a stateful version where we mutate the tree by picking a hole which
    //   has a parent pointer, for each of the expansions, modify the parent and recurse. when done,
    //   restore tree to original state
    override fun candidates(c: SearchState): Sequence<SearchState> =
        recCandidates(c, posUnification(c), sizeBound)

    private fun recCandidates(
        c: SearchState,
        unification: OneUnification,
        currSizeBound: Int
    ): Sequence<SearchState> {
        if (c.noHoles()) return sequenceOf(c)

        // We won't fast-forward label blanks that we ourselves emitted.
        if (c.noFillableHoles())
            return if (!emitLabelBlanks) conservativeFastForward(c, depthBound)
            /* conservative fast forward might return something with holes, which must be filled in a later stage as dictated by Search */
            else sequenceOf(c)

        if (currSizeBound == 0) return emptySequence()

        val (iToFill, hole, depth) = c.shallowestFillableHole() ?: error("Impossible")
        return hole
            .expansions(
                unification = unification,
                labelArities = c.labelArities,
                vars = c.types[iToFill].variables().size,
                canBeVar = hole != c.types[iToFill],
                emitLabelBlanks = emitLabelBlanks,
                mustBeLeaf = currSizeBound <= 1 || depth >= depthBound
            )
            .asSequence()
            .map {
                logger.count("Total candidates")
                c.mapTypeAtIndex(iToFill) { typ -> typ.replace(hole, it) }
            }
            .filterNot {
                // Importantly, this pruning is sound even when we perform it on outlines (before
                // label arities are computed and holes inserted accordingly). That's because when
                // we are generating outlines, labels are considered blanks
                it.types[iToFill].invalid()
            }
            .flatMap { newCandidate ->
                val u = posUnification(newCandidate)
                if (u.ok) recCandidates(newCandidate, u, currSizeBound = currSizeBound - 1)
                else emptySequence()
            }
    }
}
