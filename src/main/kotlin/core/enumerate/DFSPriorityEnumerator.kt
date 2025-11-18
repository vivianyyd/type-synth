package core.enumerate

import core.Candidate
import core.Language
import core.Unification
import core.UnificationForCandidate
import query.Query
import util.Logger

class DFSPriorityEnumerator<L : Language>(
    val query: Query,
    override val seedCandidate: Candidate<L>,
    private val unification: UnificationForCandidate<L>,
    private val mustPassNegatives: Boolean,
    private val logger: Logger,
) : Enumerator<L> {
    private fun fill(
        c: Candidate<L>,
        unification: Unification<L>,
        recursionBound: Int
    ): Sequence<Candidate<L>> {
        val (iToFill, typeToFill) = c.types.withIndex().maxBy { (_, it) -> it.priority() }

        return typeToFill
            .dfsPriorityExpansions(unification, typeToFill.variableNames().size, recursionBound)
            .asSequence()
            .mapNotNull { (newType, commit) ->
                if (commit == null) null  // generated context is the same as this one
                else Candidate(c.names, c.types.mapIndexed { i, p -> if (iToFill == i) newType else p })
            }
    }

    private fun commitPriority(
        c: Candidate<L>,
        unification: Unification<L>,
        recursionBound: Int
    ): Sequence<Candidate<L>> {
        if (c.full()) return sequenceOf(c)
        logger.count("Cands for $seedCandidate")

        return fill(c, unification, recursionBound).flatMap {
            // TODO spawnAndRefine is slow for eager unification since we make a duplicate candidate.
            //      but making a new unification is slow for other unifs.
            val u = unification(it, query.posExsBeforeSubexprs)
            if (u.ok()) {
                if (it.satisfiesDependencies())  // TODO ablate this
                    commitPriority(it, u, recursionBound)
                else emptySequence()
            } else emptySequence()
        }
    }

    override fun enumerate(maxDepth: Int): List<Candidate<L>> {
        fun check(c: Candidate<L>) =
            unification(c, query.posExsBeforeSubexprs).ok() &&
                    (if (mustPassNegatives)
                        query.negExamples.all { !unification(c, listOf(it)).ok() }
                    else true)

        return commitPriority(
            seedCandidate,
            unification(seedCandidate, query.posExsBeforeSubexprs),
            maxDepth
        ).filter { c -> check(c) }.toList()
    }
}
