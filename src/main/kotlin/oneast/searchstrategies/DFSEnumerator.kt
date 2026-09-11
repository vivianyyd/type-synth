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
    companion object {
        /**
         * Fail-fast Bottom pruning. When on, [recCandidates] returns no candidates for a state that
         * has any [OneUnification.AUResult.Bottom] hole (contradictory constructor bounds → no
         * hole-free descendant can pass positive unification). This is PURE pruning: it does not
         * change which hole is filled or in what order, so it is sound/complete and only ever removes
         * dead subtrees. Safe to leave on.
         */
        var bottomPruning = true

        /**
         * Constraint-directed (fail-first) hole ordering: fill a forced
         * [OneUnification.AUResult.Constructor] hole before any unconstrained
         * [OneUnification.AUResult.Top] hole, instead of always the structurally shallowest hole.
         *
         * DEFAULT OFF. Although reordering does not change the solution set in the LIMIT, it is NOT
         * budget-neutral in this search: the [expansions] `mustBeLeaf` guard depends on both the
         * hole's depth (`depth >= depthBound`) and `currSizeBound - holesRemaining` (open-hole count,
         * which changes with fill order). Filling deeper Constructor holes earlier makes that guard
         * bite differently, so a solution reachable at a given (size, depth) slice under shallowest
         * order can be relocated to a LARGER slice here. Under the lazy `numSols` search that means
         * MORE candidates before the first solution, not fewer (observed on the `cons` example:
         * baseline finds it at depth 2/size 5; this order does not). Needs the budget guard made
         * order-invariant before it can help. See [recCandidates].
         */
        var constructorFirstOrdering = false
    }

    // TODO can also implement a stateful version where we mutate the tree by picking a hole which
    //   has a parent pointer, for each of the expansions, modify the parent and recurse. when done,
    //   restore tree to original state
    override fun candidates(c: SearchState): Sequence<SearchState> {
        val u = posUnification(c)
        if (!u.ok) return emptySequence()
        // summaries[i] == c.types[i].shallowestFillableHole(topLevel = true); threaded down and updated
        // incrementally so recCandidates never re-walks every type on every candidate.
        val summaries = c.types.map { it.shallowestFillableHole(topLevel = true) }
        // The seed accepts the negatives only via hole constraints (it is not "failing with no hole
        // constraints"), so it already passes the negex filter — recCandidates' cIsClean invariant
        // holds for the root, and we take its default.
        return recCandidates(c, u, sizeBound, c.numFillableHoles(), summaries, false)
    }

    /**
     * As long as seed [c] passes positive examples, states returned by this function do as well.
     *
     * Negex reuse: children are only recursed on after surviving the negex filter, so every state
     * reaching here already passes every negative example — that is the [cIsClean] invariant. Given
     * it, filling a hole changes exactly one component's type, so only negatives that *reference that
     * component* can flip verdict; the rest stay non-failing. So a clean parent's children need only
     * re-check those [affected] negs, not all of them. The one operation that breaks the invariant is
     * the label-blanking rewrite below: it strips constraints off many types at once and can re-dirty
     * a clean state, so it recurses with [cIsClean] = false, which falls back to the full negex check
     * until cleanliness is re-established. All other call sites (root and normal recursion) keep the
     * `true` default.
     *
     * [summaries] holds, per index in [c].types, that type's shallowest fillable hole (or null) —
     * `c.types[i].shallowestFillableHole(topLevel = true)`. Threaded down and updated incrementally
     * (only the one changed index is recomputed) so we avoid re-walking the whole state per candidate.
     */
    private fun recCandidates(
        c: SearchState,
        unification: OneUnification,
        currSizeBound: Int,
        holesRemaining: Int,
        summaries: List<Pair<TypeHole, Int>?>,
        cIsClean: Boolean = true
    ): Sequence<SearchState> {
//        unification.log(logger)
//        logger.log("$c")
        // summaries.all { it == null } subsumes both the old c.noHoles() and c.noFillableHoles()
        // early returns (both returned sequenceOf(c)) without re-walking every type.
        if (summaries.all { it == null }) return sequenceOf(c)
//            return if (!emitLabelBlanks) unionFastForward(c, depthBound)
//            else sequenceOf(c)

        if (currSizeBound - holesRemaining < 0) return emptySequence()

        // Reproduce SearchState.shallowestFillableHole exactly: scan indices ascending, keep the
        // minimum-depth hole, lowest index winning ties (what minByOrNull over withIndex does).
        val shallowest = summaries
            .withIndex()
            .mapNotNull { (i, s) -> s?.let { i to it } }
            .minByOrNull { it.second.second }
            ?.let { Triple(it.first, it.second.first, it.second.second) }
            ?: error("Impossible")

        // Bottom-pruning is sound: a Bottom hole has contradictory constructor bounds, so every
        // concrete filling of it fails positive unification and no hole-free descendant is a
        // solution. It keeps the shallowest fill order, so it only removes dead subtrees.
        // constructorFirstOrdering additionally reorders which hole is filled (see companion doc for
        // why it is off by default).
        val (iToFill, hole, depth) =
            if (!bottomPruning && !constructorFirstOrdering) shallowest
            else {
                // Classify ALL fillable holes (not just the per-type shallowest) by what unification
                // already knows.
                val holes = c.fillableHolesWithDepth()
                // Parity: the minimum-depth hole (lowest index on ties) equals shallowestFillableHole.
                check(holes.minByOrNull { it.third } == shallowest) {
                    "TEMP: fillableHolesWithDepth parity broken for $c"
                }
                val classified = holes.map { it to unification.antiunifyRoots(it.second) }
                // Bottom → this candidate provably has no solution; prune the whole subtree now.
                if (bottomPruning && classified.any { it.second == OneUnification.AUResult.Bottom })
                    return emptySequence()
                if (!constructorFirstOrdering) shallowest
                // Prefer a forced Constructor hole (narrow fanout, propagates constraints through the
                // union-find); else the shallowest Top hole == shallowestFillableHole() by parity.
                else classified
                    .filter { it.second is OneUnification.AUResult.Constructor }
                    .map { it.first }
                    .ifEmpty { holes }
                    .minByOrNull { it.third }!!
            }
//        println("Expanding ${c.names.filterValues { it==iToFill }}: ${c.types[iToFill].debugString()}")
//        println(unification.boundConstructors(hole))
        // Every expansion at this node fills a hole at the same [iToFill], so they all modify the
        // same component name(s) and thus affect the same set of neg examples. Compute it once: the
        // name(s) at iToFill, then the negs mentioning any of them.
        val affected: List<Int> =
            c.names.entries.filter { it.value == iToFill }
                .flatMap { affectedNegs[it.key].orEmpty() }
                .distinct()
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
            .filterNot { (_, newCandidate) ->
//                logger.log("expand to $newCandidate")
//                val s = newCandidate.toString()
//                if (s.contains("{b=L0[], put=L1[V0, V1] -> V0 -> V1 -> L1[V0, V1]}") || s.contains("chain=L1[V0"))
//                    logger.log(s)
                // Given the cIsClean invariant, only the [affected] negs can have changed from [c];
                // re-check just those. Otherwise ([cIsClean] = false, i.e. after the label-blanking
                // rewrite) fall back to the full negex check.
                if (cIsClean) affected.any { negVerdict(newCandidate, it) }
                else failsNegexWithNoHoleConstraints(newCandidate)
            }
            .flatMap { (introducedHoles, newCandidate) ->
                val u = posUnification(newCandidate)
                if (u.ok) {
                    // Only iToFill's type changed, so copy summaries and recompute just that index.
                    val newSummaries = summaries.toMutableList().also {
                        it[iToFill] = newCandidate.types[iToFill].shallowestFillableHole(topLevel = true)
                    }
                    // newCandidate survived the negex filter, so the cIsClean invariant holds: default.
                    recCandidates(
                        newCandidate,
                        u,
                        currSizeBound = currSizeBound - 1,
                        holesRemaining = holesRemaining - 1 + introducedHoles,
                        summaries = newSummaries
                    )
                } else if (emitLabelBlanks && u.badLabels().isNotEmpty()) {
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
                    // This blanks labels across many types at once, stripping constraints, so it can
                    // re-dirty a clean state: the cIsClean invariant no longer holds. Recurse with
                    // cIsClean = false so children get the full negex check until it is re-established.
                    recCandidates(
                        badLabelsBlanked,
                        u,
                        currSizeBound = currSizeBound - 1,
                        holesRemaining = badLabelsBlanked.numFillableHoles(),
                        // Many types change here, so incremental summary updates don't apply; recompute.
                        summaries = badLabelsBlanked.types.map { it.shallowestFillableHole(topLevel = true) },
                        cIsClean = false
                    )
                } else emptySequence()
            }
    }
}
