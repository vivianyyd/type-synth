package oneast.searchstrategies

import oneast.OneUnification
import oneast.SearchState
import oneast.Type
import query.Examples
import util.Logger

class MutatingDFS(
    examples: Examples,
    private val emitLabelBlanks: Boolean,
    private val sizeBound: Int,
    private val depthBound: Int,
    private val logger: Logger
) : SearchStrategy(examples) {
    override fun candidates(c: SearchState): Sequence<SearchState> =
        recCandidates(c, posUnification(c), sizeBound)

    private fun recCandidates(
        c: SearchState,
        unification: OneUnification,
        currSizeBound: Int
    ): Sequence<SearchState> = sequence {
        /*
        searchRec()
            hole = pop
            for exp in expansions
                [check types, compatibility, size bound]
                expand(hole, exp)
                if more holes:
                    searchRec
                else
                    evaluate solution
                unexpand(hole, exp)
            push(hole)
         */
        if (c.noHoles()) {
            yield(c)
            return@sequence
        }
        if (c.noFillableHoles()) {
            if (!emitLabelBlanks) yieldAll(fastForward(c)) else yield(c)
            return@sequence
        }
        if (currSizeBound == 0) return@sequence

        val (iToFill, hole, depth) = c.shallowestFillableHole() ?: error("Impossible")

        val topLevel = hole == c.types[iToFill]
        fun replaceInTy(target: Type, replacement: Type) {
            if (topLevel) c.types[iToFill] = replacement
            else c.types[iToFill].replaceInPlace(target, replacement)
        }

        val expansions =
            hole
                .expansions(
                    unification = unification,
                    labelArities = c.labelArities,
                    vars = c.types[iToFill].variables().size,
                    canBeVar = hole != c.types[iToFill],
                    emitLabelBlanks = emitLabelBlanks,
                    mustBeLeaf = currSizeBound <= 1 || depth >= depthBound
                )
                .asSequence()
        for (exp in expansions) {
            logger.count("Total candidates")
            replaceInTy(hole, exp)
            if (!c.types[iToFill].invalid()) {
                val u = posUnification(c)
                if (u.ok()) yieldAll(recCandidates(c, u, currSizeBound = currSizeBound - 1))
            }
            replaceInTy(exp, hole)
        }
    }
}
