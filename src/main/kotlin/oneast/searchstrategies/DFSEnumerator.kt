package oneast.searchstrategies

import bench.Count
import bench.Stats
import oneast.*
import query.Examples

/** Fills one hole at a time, shallowest first, in DFS style. */
class DFSEnumerator(
    examples: Examples,
    private val emitLabelBlanks: Boolean,
    private val emitConstructors: Boolean,
    private val sizeBound: Int,
    private val depthBound: Int,
    /** See [oneast.Configuration.expansions]. */
    private val expansions: Expansions,
    /**
     * Gets the labels whenever the positive examples need two labels to be equal: when a state fails
     * to unify because of them, or when a hole is unified with both.
     */
    private val clashes: MutableSet<Set<Int>>,
) : SearchStrategy(examples) {
    override fun candidates(c: SearchState): Sequence<SearchState> {
        val u = posUnification(c)
        return if (u.satisfiable()) recCandidates(c, u, sizeBound, c.numFillableHoles())
        else {
            clash(u.badLabels())
            Stats.inc(Count.PRUNED_POS)
            emptySequence()
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
     */
    private fun recCandidates(
        c: SearchState,
        unification: OneUnification,
        currSizeBound: Int,
        holesRemaining: Int
    ): Sequence<SearchState> {
        // Before either return below, so that outlines, including those with no blanks left, are
        // checked before label arities are solved for.
        if (c.acceptsANegative(examples.neg)) {
            Stats.inc(Count.PRUNED_NEG)
            Stats.trace("prunedNeg") { c }
            return emptySequence()
        }

        if (c.noHoles()) return sequenceOf(c)

        if (c.noFillableHoles()) return sequenceOf(c)

        if (currSizeBound - holesRemaining < 0) return emptySequence()

        val (iToFill, hole, depth) = c.shallowestFillableHole() ?: error("Impossible")
        (unification.holeConstructor(hole) as? HoleConstructor.Conflicting)?.let { clash(it.labels) }
        val mark = unification.mark()
        return hole
            .expansions(
                unification = unification,
                labelArities = c.labelArities,
                vars = c.types[iToFill].variables().size,
                canBeVar = hole != c.types[iToFill],
                emitLabelBlanks = emitLabelBlanks,
                emitConstructors = emitConstructors,
                mustBeLeaf = currSizeBound - holesRemaining <= 1 || depth >= depthBound,
                kind = expansions
            )
            .asSequence()
            .flatMap { expansion ->
                unification.rewindTo(mark)
                Stats.inc(Count.CANDIDATES)
                val newCandidate = c.mapTypeAtIndex(iToFill) { typ -> typ.replace(hole, expansion) }
                if (unification.refine(hole, expansion)) {
                    Stats.trace("candidate") { newCandidate }
                    recCandidates(
                        newCandidate,
                        unification,
                        currSizeBound = currSizeBound - 1,
                        holesRemaining = holesRemaining - 1 + expansion.numFillableHoles()
                    )
                } else {
                    Stats.inc(Count.PRUNED_POS)
                    Stats.trace("prunedPos") { newCandidate }
                    clash(unification.badLabels())
                    emptySequence()
                }
            }
    }

    /** Adds [labels] to [clashes], unless there are none. */
    private fun clash(labels: Set<Int>) {
        if (labels.isNotEmpty()) clashes.add(labels)
    }
}
