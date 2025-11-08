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
    private fun commitPriority(
        c: Candidate<L>,
        unification: Unification<L>,
        recursionBound: Int
    ): Sequence<Candidate<L>> {
        val (changeInd, prioritized) = c.types.withIndex().maxByOrNull { (_, it) -> it.priority() }
            ?: return sequenceOf(c)
        if (prioritized.priority() == 0) return sequenceOf(c)

        val optionsForPrioritized =
            prioritized.dfsPriorityExpansions(unification, prioritized.variableNames(), recursionBound).asSequence()
        return optionsForPrioritized.flatMap { (newType, commit) ->
            val newCandidate = Candidate(c.names, c.types.mapIndexed { i, p -> if (changeInd == i) newType else p })
            if (commit == null) {
                require(newCandidate == c)
                emptySequence() // this call made no changes, but we don't want to hit it again TODO verify this doesn't break completeness
            } else {
                val u = unification.spawnAndRefine(listOf(commit))
                if (u.ok()) {
                    // TODO ablate this
                    if (newCandidate.satisfiesDependencies())
                        commitPriority(newCandidate, u, recursionBound)
                    else emptySequence()

                } else emptySequence()
            }
        }
    }

    override fun enumerate(maxDepth: Int): List<Candidate<L>> {
        fun check(c: Candidate<L>) =
            unification(c, query.posExsBeforeSubexprs).ok() &&
                    (if (mustPassNegatives)
                        query.negExamples.all { !unification(c, listOf(it)).ok() }
                    else true)

        // Check for non null seed; this should only be necessary for the first round, since some Init seeds may be unsat
        // TODO check that indeed only the Init seeds fail here
        val u = unification(seedCandidate, query.posExsBeforeSubexprs)
        if (!u.ok()) return listOf()
        return commitPriority(
            seedCandidate,
            u,
            maxDepth
        ).filter { c -> c.canonical() && check(c) }.toList()
    }
}
