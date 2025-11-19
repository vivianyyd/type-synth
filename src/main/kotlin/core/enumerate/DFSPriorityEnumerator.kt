package core.enumerate

import core.Candidate
import core.Language
import core.Unification
import core.UnificationForCandidate
import query.Query
import util.Bound
import util.BoundTag.Choice
import util.BoundTag.Depth
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
        bound: Bound
    ): Sequence<Candidate<L>> {
        val (iToFill, typeToFill) = c.types.withIndex().maxBy { (_, it) -> it.priority() }

        val mustBeLeaf = when (bound.type) {
            Depth -> false
            Choice -> bound.b <= 1
        }

        // New version doesn't use SearchNode-specified expansions for each node, only for the holes
        val holeToFill = typeToFill.listHoles().maxBy { it.priority() }
        return holeToFill.expansions(unification, typeToFill.variableNames().size, mustBeLeaf).asSequence()
            .mapNotNull { holeFill ->
                val t = typeToFill.replace(holeToFill, holeFill)
                if (bound.type == Depth && t.depth() > bound.b) null
                else t  // TODO the hole should just store its own depth and we query that to figure out if it must be leaf. then no need to filter this late
            }
            .map { newType ->
                Candidate(c.names, c.types.mapIndexed { i, p -> if (iToFill == i) newType else p })
            }
    }

    private fun commitPriority(
        c: Candidate<L>,
        unification: Unification<L>,
        bound: Bound
    ): Sequence<Candidate<L>> {
        if (c.full()) return sequenceOf(c)
        logger.count("Cands for $seedCandidate")

        val nextBound = when (bound.type) {
            Depth -> bound
            Choice -> {
                if (bound.b == 0) return sequenceOf()
                bound.copy(b = bound.b - 1)
            }
        }

        return fill(c, unification, bound).flatMap {
            // TODO spawnAndRefine is slow for eager unification since we make a duplicate candidate.
            //      but making a new unification is slow for other unifs.
            val u = unification(it, query.posExsBeforeSubexprs)
            if (u.ok()) {
                if (it.satisfiesDependencies())  // TODO ablate this
                    commitPriority(it, u, nextBound)
                else emptySequence()
            } else emptySequence()
        }
    }

    override fun enumerate(bound: Bound): List<Candidate<L>> {
        fun check(c: Candidate<L>) =
            unification(c, query.posExsBeforeSubexprs).ok() &&
                    (if (mustPassNegatives)
                        query.negExamples.all { !unification(c, listOf(it)).ok() }
                    else true)

        return commitPriority(
            seedCandidate,
            unification(seedCandidate, query.posExsBeforeSubexprs),
            bound
        ).filter { c -> check(c) }.toList()
    }
}
