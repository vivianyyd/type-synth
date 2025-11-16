package core.enumerate

import core.Candidate
import core.Language
import core.Unification
import core.UnificationForCandidate
import query.Query
import util.Logger

class DFSLeftEnumerator<L : Language>(
    val query: Query,
    override val seedCandidate: Candidate<L>,
    private val unification: UnificationForCandidate<L>,
    private val mustPassNegatives: Boolean,
    private val logger: Logger,
) : Enumerator<L> {
    private fun commitLeftmost(
        c: Candidate<L>,
        unification: Unification<L>,
        recursionBound: Int
    ): Sequence<Candidate<L>> {
        val (changeInd, leftmostNode) = c.types.withIndex().firstOrNull { (_, it) -> it.holes() > 0 }
            ?: return sequenceOf(c)

        val optionsForLeftmost =
            leftmostNode.dfsLeftExpansions(unification, leftmostNode.variableNames().size, recursionBound).asSequence()

        return optionsForLeftmost.flatMap { (newLeftMost, commit) ->
            val newCandidate = Candidate(c.names, c.types.mapIndexed { i, p -> if (changeInd == i) newLeftMost else p })
            if (commit == null) {
                require(newCandidate == c)
                emptySequence() // this call made no changes, but we don't want to hit it again TODO verify this doesn't break completeness
            } else {
                // We reconstruct Unification every time because we don't want different child branches to
                //  affect one another, and Unification is stateful.
                val u = unification.spawnAndRefine(listOf(commit))
                if (u.ok())
                    commitLeftmost(newCandidate, u, recursionBound)
                else emptySequence()
            }
        }
    }

    override fun enumerate(maxDepth: Int): List<Candidate<L>> {
        fun check(c: Candidate<L>) =
            unification(c, query.posExsBeforeSubexprs).ok() &&
                    (if (mustPassNegatives)
                        query.negExamples.all { !unification(c, listOf(it)).ok() }
                    else true)

        val u = unification(seedCandidate, query.posExsBeforeSubexprs)
        if (!u.ok()) return listOf()
        return commitLeftmost(
            seedCandidate,
            u,
            maxDepth
        ).filter { c -> check(c) }.toList()
    }
}
