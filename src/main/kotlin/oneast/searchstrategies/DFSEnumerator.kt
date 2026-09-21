package oneast.searchstrategies

import oneast.*
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
        return if (u.ok) recCandidates(c, u, sizeBound, c.numFillableHoles())
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

        if (c.noFillableHoles()) return sequenceOf(c)

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
            .flatMap { (introducedHoles, newCandidate) ->
                // TODO: prune using negative examples.
                val u = posUnification(newCandidate)
                if (u.ok)
                    recCandidates(
                        newCandidate,
                        u,
                        currSizeBound = currSizeBound - 1,
                        holesRemaining = holesRemaining - 1 + introducedHoles
                    )
                else retryWithoutBadLabels(newCandidate, u.badLabels(), currSizeBound)
            }
    }

    /**
     * If we failed only because two distinct labels had to be equal, those labels were guesses we
     * are free to take back: blank them out and enumerate them again.
     *
     * TODO: Not sure how to guarantee termination. I think it holds because we only backtrack if
     *       there are distinct labels to merge. Does this introduce duplicates?
     */
    private fun retryWithoutBadLabels(
        c: SearchState,
        badLabels: Set<Int>,
        currSizeBound: Int
    ): Sequence<SearchState> {
        if (!emitLabelBlanks || badLabels.isEmpty()) return emptySequence()
        // A bad label that is committed cannot be rewritten, so there is no solution.
        if (badLabels.any { it in c.committedLabels }) return emptySequence()

        fun blankBadLabels(t: Type): Type =
            when (t) {
                is Arrow -> Arrow(blankBadLabels(t.l), blankBadLabels(t.r))
                is NamedLabel ->
                    if (t.label in badLabels) Blank(labelOnly = true)
                    else t.copy(params = t.params.map { blankBadLabels(it) })
                is THole,
                is Variable -> t
            }

        val blanked =
            c.mapTypesAndSetLabelArities(
                newArities = c.labelArities.filterNot { (l, _) -> l in badLabels }
            ) { blankBadLabels(it) }
        // The labels changed everywhere at once, so this subtree needs a check of its own.
        val unification = posUnification(blanked)
        return if (unification.ok)
            recCandidates(blanked, unification, currSizeBound - 1, blanked.numFillableHoles())
        else emptySequence()
    }
}
