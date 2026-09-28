package oneast.searchstrategies

import oneast.*
import query.Example
import query.Examples
import util.Logger

/** Fills one hole at a time, shallowest first, in DFS style. */
class DFSEnumerator(
    examples: Examples,
    private val emitLabelBlanks: Boolean,
    private val emitConstructors: Boolean,
    private val sizeBound: Int,
    private val depthBound: Int,
    private val logger: Logger,
    /**
     * Whether a node re-checks only the negative examples its last fill can have changed the
     * verdict on, rather than all of them. Only there to test that doing so changes nothing.
     */
    private val checkOnlyAffectedNegatives: Boolean = true
) : SearchStrategy(examples) {
    /**
     * Whether the search has stopped changing labels other than by filling holes. While it emits
     * label blanks, it is outlining: it blanks out labels that clash, and label arities are decided
     * after it returns.
     */
    private val labelsSettled = !emitLabelBlanks

    override fun candidates(c: SearchState): Sequence<SearchState> {
        val u = posUnification(c)
        // Nothing has checked the seed yet.
        return if (u.ok)
            recCandidates(c, u, sizeBound, c.numFillableHoles(), examples.neg, negativesAt(c))
        else emptySequence()
    }

    /**
     * For each type index of [c], the negative examples that mention a name whose type it is.
     *
     * Type-checking an example instantiates only the types of the names it mentions, so filling a
     * hole in one type can change the verdict only on the negatives listed at its index. Every way
     * the search changes a state keeps [SearchState.names], so this holds for all of [c]'s subtree.
     */
    private fun negativesAt(c: SearchState): List<List<Example>> {
        if (!checkOnlyAffectedNegatives) return List(c.types.size) { examples.neg }
        return c.types.indices.map { i ->
            examples.neg.filter { ex -> ex.names.any { c.names[it] == i } }
        }
    }

    /**
     * As long as seed [c] passes positive examples, states returned by this function do as well.
     *
     * [unification] is the running check for [c]. Each expansion refines it in place and rewinds
     * afterwards, so the whole subtree shares one set of equivalence classes rather than rebuilding
     * them per candidate. Rewinding happens before an expansion rather than after, which is what
     * makes this safe to consume lazily: a subtree that is abandoned half-way leaves the check
     * dirty, and whoever resumes cleans it up first.
     *
     * [negatives] are those whose verdict can differ from the one they had at [c]'s parent. The
     * parent accepted none of the negatives, or it would have no children, so a negative left out
     * still is not accepted. That is only so for a parent that changed in one type; when more
     * changed, or there is no parent, pass all of them.
     */
    private fun recCandidates(
        c: SearchState,
        unification: OneUnification,
        currSizeBound: Int,
        holesRemaining: Int,
        negatives: List<Example>,
        negativesAt: List<List<Example>>
    ): Sequence<SearchState> {
        // Before either return below, so that outlines, including those with no blanks left, are
        // checked before label arities are solved for.
        if (c.acceptsANegative(negatives, labelsSettled)) {
            logger.count("Pruned by negative examples")
            return emptySequence()
        }

        if (c.noHoles()) return sequenceOf(c)

        if (c.noFillableHoles()) return sequenceOf(c)

        if (currSizeBound - holesRemaining < 0) return emptySequence()

        val (iToFill, hole, depth) = c.shallowestFillableHole() ?: error("Impossible")
        val mark = unification.mark()
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
            .flatMap { expansion ->
                unification.rewindTo(mark)
                logger.count("Total candidates")
                val newCandidate = c.mapTypeAtIndex(iToFill) { typ -> typ.replace(hole, expansion) }
                if (unification.refine(hole, expansion))
                    recCandidates(
                        newCandidate,
                        unification,
                        currSizeBound = currSizeBound - 1,
                        holesRemaining = holesRemaining - 1 + expansion.numFillableHoles(),
                        negatives = negativesAt[iToFill],
                        negativesAt = negativesAt
                    )
                else retryWithoutBadLabels(newCandidate, unification.badLabels(), currSizeBound, negativesAt)
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
        currSizeBound: Int,
        negativesAt: List<List<Example>>
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
        // The labels changed everywhere at once, so this subtree needs a check of its own, and so
        // do the negatives.
        val unification = posUnification(blanked)
        return if (unification.ok)
            recCandidates(
                blanked,
                unification,
                currSizeBound - 1,
                blanked.numFillableHoles(),
                examples.neg,
                negativesAt
            )
        else emptySequence()
    }
}
