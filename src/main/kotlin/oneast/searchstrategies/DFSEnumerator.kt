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
    override fun candidates(c: SearchState): Sequence<SearchState> {
        val checks = Checks(c, examples)
        return if (checks.pos.ok) recCandidates(c, checks, 0, sizeBound, c.numFillableHoles())
        else emptySequence()
    }

    /**
     * As long as seed [c] passes positive examples, states returned by this function do as well.
     *
     * [checks] is the running check for [c]. Each expansion refines it in place and rewinds
     * afterwards, so the whole subtree shares one set of equivalence classes rather than rebuilding
     * them per candidate. Rewinding happens before an expansion rather than after, which is what
     * makes this safe to consume lazily: a subtree that is abandoned half-way leaves the check
     * dirty, and whoever resumes cleans it up first.
     */
    private fun recCandidates(
        c: SearchState,
        checks: Checks,
        depth: Int,
        currSizeBound: Int,
        holesRemaining: Int
    ): Sequence<SearchState> {
        if (c.noHoles()) return sequenceOf(c)

        // We won't fast-forward label blanks that we ourselves emitted.
        if (c.noFillableHoles())
            return if (!emitLabelBlanks) unionFastForward(c, depthBound)
            else sequenceOf(c)

        if (currSizeBound - holesRemaining < 0) return emptySequence()

        val (iToFill, hole, holeDepth) = c.shallowestFillableHole() ?: error("Impossible")
        checks.save(depth)
        return hole
            .expansions(
                unification = checks.pos,
                labelArities = c.labelArities,
                vars = c.types[iToFill].variables().size,
                canBeVar = hole != c.types[iToFill],
                emitLabelBlanks = emitLabelBlanks,
                emitConstructors = emitConstructors,
                mustBeLeaf = currSizeBound - holesRemaining <= 1 || holeDepth >= depthBound
            )
            .asSequence()
            .flatMap { expansion ->
                checks.restore(depth)
                logger.count("Total candidates")
                val newCandidate = c.mapTypeAtIndex(iToFill) { typ -> typ.replace(hole, expansion) }
                val stillPasses = checks.refine(iToFill, hole, expansion)
                when {
                    checks.someNegexPasses() -> emptySequence()
                    stillPasses ->
                        recCandidates(
                            newCandidate,
                            checks,
                            depth = depth + 1,
                            currSizeBound = currSizeBound - 1,
                            holesRemaining = holesRemaining - 1 + expansion.numFillableHoles()
                        )
                    else ->
                        retryWithoutBadLabels(newCandidate, checks.pos.badLabels(), currSizeBound)
                }
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
        val checks = Checks(blanked, examples)
        return if (checks.pos.ok)
            recCandidates(blanked, checks, 0, currSizeBound - 1, blanked.numFillableHoles())
        else emptySequence()
    }
}
