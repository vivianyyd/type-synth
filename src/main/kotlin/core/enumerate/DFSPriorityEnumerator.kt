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
        mustBeLeaf: Boolean
    ): Sequence<Candidate<L>> {
        val (iToFill, typeToFill) = c.types.withIndex()
            .maxBy { (_, it) -> it.priority() }  // todo want to order by hole depth, then remove bound on iterative deepening thing

        // New version doesn't use SearchNode-specified expansions for each node, only for the holes
        val holeToFill = typeToFill.listHoles().maxBy { it.priority() }
        return holeToFill.expansions(unification, typeToFill.variableNames().size, mustBeLeaf).asSequence()
            .map { holeFill -> typeToFill.replace(holeToFill, holeFill) }
            .map { newType ->
                Candidate(c.names, c.types.mapIndexed { i, p -> if (iToFill == i) newType else p })
            }
    }

    private fun commitPriority(
        c: Candidate<L>,
        unification: Unification<L>,
        sizeBound: Int,
        hardDepthBound: Int
    ): Sequence<Candidate<L>> {
        logger.count("Cands under $seedCandidate")
        logger.log("Exploring $c")
        if (c.full()) {
            logger.count("Cand under $seedCandidate passed all posexs")
            return sequenceOf(c)
        }
        if (sizeBound == 0) {
            logger.count("Hit size bound under $seedCandidate")
            val ff = c.fastForward(unification) ?: return sequenceOf()
            return if (ff.full()) {
                logger.count("Fast forwarded for $seedCandidate")
                logger.log("\tFast forwarded from\n\t\t$c\n\t\t$ff")
                sequenceOf(ff)
            } else sequenceOf()
        }

        return fill(c, unification, sizeBound <= 1).flatMap {
            if (it.depth() > hardDepthBound) emptySequence()
            else {
                // TODO spawnAndRefine is slow for eager unification since we make a duplicate candidate.
                //      but making a new unification is slow for other unifs.
                val u = unification(it, query.posExsBeforeSubexprs)
                if (u.ok()) {
                    if (it.satisfiesDependencies())  // TODO ablate this
                        commitPriority(it, u, sizeBound - 1, hardDepthBound)
                    else emptySequence()
                } else emptySequence()
            }
        }
    }

    override fun enumerate(sizeBound: Int, hardDepthBound: Int): List<Candidate<L>> {
        fun check(c: Candidate<L>) =
            unification(c, query.posExsBeforeSubexprs).ok() &&
                    (if (mustPassNegatives)
                        query.negExamples.all { !unification(c, listOf(it)).ok() }
                    else true)

        return commitPriority(
            seedCandidate,
            unification(seedCandidate, query.posExsBeforeSubexprs),
            sizeBound,
            hardDepthBound
        ).filter { c -> check(c) }.toList()
    }
}
