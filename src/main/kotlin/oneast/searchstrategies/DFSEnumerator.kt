package oneast.searchstrategies

import oneast.OneUnification
import oneast.SearchState
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
        emitLabelBlanks: Boolean,
        sizeBound: Int,
        depthBound: Int,
        logger: Logger
    ): Sequence<SearchState> {
        if (c.noHoles()) return sequenceOf(c)

        // We won't fast-forward label blanks that we ourselves emitted.
        if (c.noFillableHoles()) return if (!emitLabelBlanks) fastForward(c) else sequenceOf(c)

        if (sizeBound == 0) return emptySequence()

        val (iToFill, holeWithDepth) = c.shallowestFillableHole() ?: error("Impossible")
        val (hole, depth) = holeWithDepth
        return hole
            .expansions(
                unification = unification,
                labelArities = c.labelArities,
                vars = c.types[iToFill].variables().size,
                topLevel = hole == c.types[iToFill],
                emitLabelBlanks = emitLabelBlanks,
                mustBeLeaf = sizeBound <= 1 || depth >= depthBound
            )
            .asSequence()
            .map { c.mapTypeAtIndex(iToFill) { typ -> typ.replace(hole, it) } }
            .filterNot {
                // Importantly, this pruning is sound even when we perform it on outlines (before
                // label arities are computed and holes inserted accordingly). That's because when
                // we are generating outlines, labels are considered blanks
                it.types[iToFill].invalid()
            }
            .flatMap { newCandidate ->
                logger.count("Total candidates")
                val u = posUnification(newCandidate)
                if (u.ok()) {
                    candidates(newCandidate, u, emitLabelBlanks, sizeBound - 1, depthBound, logger)
                } else emptySequence()
            }
    }
}
