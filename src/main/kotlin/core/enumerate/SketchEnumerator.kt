package core.enumerate

import core.languages.Candidate
import core.languages.Language
import core.unification.UnificationForCandidate
import query.Query
import util.Logger

class SketchEnumerator<L : Language>(
    val query: Query,
    override val seedCandidate: Candidate<L>,
    private val unification: UnificationForCandidate<L>,
    private val mustPassNegatives: Boolean,
    private val logger: Logger,
) : Enumerator<L> {
    //    private fun fill(
    //        s: Candidate<L>,
    //        unification: Unification<L>,
    //        recursionBound: Int
    //    ): Sequence<Candidate<L>> {
    //        val (iToFill, typeToFill) = c.types.withIndex().maxBy { (_, it) -> it.priority() }
    //
    //        return typeToFill
    //            .dfsPriorityExpansions(unification, typeToFill.variableNames().size,
    // recursionBound)
    //            .asSequence()
    //            .mapNotNull { (newType, commit) ->
    //                if (commit == null) null  // generated context is the same as this one
    //                else Candidate(c.names, c.types.mapIndexed { i, p -> if (iToFill == i) newType
    // else p })
    //            }
    //    }

    /**
     * We can make blanks a searchnode <concrete>! or we can just make a custom language just for
     * the final round
     *
     * then can we use dfspriorityenumerator directly?
     */

    //    private fun commitPriority(
    //        c: Candidate<L>,
    //        unification: Unification<L>,
    //        recursionBound: Int
    //    ): Sequence<Candidate<L>> {
    //        if (c.full()) return sequenceOf(c)
    //        logger.count("Cands for $seedCandidate")
    //
    //        return fill(c, unification, recursionBound).flatMap {
    //            // TODO spawnAndRefine is slow for eager unification since we make a duplicate
    // candidate.
    //            //      but making a new unification is slow for other unifs.
    //            val u = unification(it, query.posExsBeforeSubexprs)
    //            if (u.ok()) {
    //                if (it.satisfiesDependencies())  // TODO ablate this
    //                    commitPriority(it, u, recursionBound)
    //                else emptySequence()
    //            } else emptySequence()
    //        }
    //    }

    override fun enumerate(
        sketches: Boolean,
        sizeBound: Int,
        hardDepthBound: Int
    ): List<Candidate<L>> {
        fun check(c: Candidate<L>) =
            unification(c, query.posNoSubexprs).ok() &&
                    (if (mustPassNegatives) query.neg.all { !unification(c, listOf(it)).ok() }
                    else true)

        return TODO()
        //        commitPriority(
        //            seedCandidate,
        //            unification(seedCandidate, query.posExsBeforeSubexprs),
        //            maxDepth
        //        ).filter { c -> check(c) }.toList()
    }
}
