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
     *
     * [negVerdicts] holds, for each negative example, whether it passes-with-no-constraints against
     * [c] (i.e. whether [c] would fail the negex filter on it). It is threaded down the recursion and
     * updated incrementally: filling a hole modifies exactly one component's type, so only negs that
     * reference that component can change verdict; the rest are inherited unchanged.
     */
    private fun recCandidates(
        c: SearchState,
        unification: OneUnification,
        currSizeBound: Int,
        holesRemaining: Int,
        negVerdicts: BooleanArray,
        reverseNames: Map<Int, List<String>>
    ): Sequence<SearchState> {
        //        println("$c")
        if (c.noHoles()) return sequenceOf(c)

        // We won't fast-forward label blanks that we ourselves emitted.
        if (c.noFillableHoles()) return sequenceOf(c)
            // return if (!emitLabelBlanks) unionFastForward(c, depthBound)
            // else sequenceOf(c)

        if (currSizeBound - holesRemaining < 0) return emptySequence()

        val (iToFill, hole, depth) = c.shallowestFillableHole() ?: error("Impossible")
//        println("Expanding ${c.names.filterValues { it==iToFill }}: ${c.types[iToFill].debugString()}")
//        println(unification.boundConstructors(hole))
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
                else if (emitLabelBlanks && u.badLabels().isNotEmpty()) {
                    // A bad label that is committed cannot be rewritten, so there is no solution.
                    if (u.badLabels().any { it in newCandidate.committedLabels })
                        return@flatMap emptySequence<SearchState>()
                    // If we failed because we tried to unify distinct labels, we should regenerate those labels.
                    // TODO: Not sure how to guarantee termination. I think it holds because we only backtrack
                    //       if there are distinct labels to merge. Does this introduce duplicates?
                    fun replaceBadLabelsWithBlanks(t: Type): Type =
                        when (t) {
                            is Arrow ->
                                Arrow(
                                    replaceBadLabelsWithBlanks(t.l),
                                    replaceBadLabelsWithBlanks(t.r)
                                )
                            is NamedLabel ->
                                if (t.label in u.badLabels()) Blank(labelOnly = true)
                                else
                                    t.copy(params = t.params.map { replaceBadLabelsWithBlanks(it) })
                            is THole,
                            is Variable -> t
                        }

                    val badLabelsBlanked = newCandidate.mapTypesAndSetLabelArities(
                        newArities = newCandidate.labelArities.filterNot { (l, _) -> l in u.badLabels() }
                    ) { replaceBadLabelsWithBlanks(it) }
                    recCandidates(
                        badLabelsBlanked,
                        u,
                        currSizeBound = currSizeBound - 1,
                        holesRemaining = badLabelsBlanked.numFillableHoles()
                    )
                } else emptySequence()
            }
    }
}
