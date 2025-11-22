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
    /** Fills one hole. Returns the resulting Candidate and the cost of that single commitment made. */
    private fun fill(
        c: Candidate<L>,
        unification: Unification<L>,
        mustBeLeaf: Boolean
    ): Sequence<Pair<Candidate<L>, Int>> {
        val (iToFill, typeToFill) = c.types.withIndex()
            .maxBy { (_, it) -> it.priority() }  // todo want to order by hole depth, then remove bound on iterative deepening thing

        // New version doesn't use SearchNode-specified expansions for each node, only for the holes
        val holeToFill = typeToFill.fillable().maxBy { it.priority() }
        return holeToFill.expansions(unification, typeToFill.variableNames().size, mustBeLeaf).asSequence()
            .map { holeFill -> typeToFill.replace(holeToFill, holeFill) to holeFill.costToCommit() }
            .map { (newType, cost) ->
                Candidate(c.names, c.types.mapIndexed { i, p -> if (iToFill == i) newType else p }) to cost
            }
    }

    private fun commitPriority(
        c: Candidate<L>,
        unification: Unification<L>,
        sizeBound: Int,
        hardDepthBound: Int
    ): Sequence<Candidate<L>> {
        logger.count("Cands under $seedCandidate")
        if (c.full()) return sequenceOf(c)

        if (c.toString().contains("put: L1[V0, V1] -> V0 -> V1 -> L1[V0, V1]")) {
            println("HELLO I am $c")
            println("Fast forward:")
            println(c.fastForward(unification))
            TODO()
        }


        if (c.types.all { it.fillable().isEmpty() }) {
            logger.count("Only blanks left under $seedCandidate")
            logger.count("Trying ff for $seedCandidate")
            val ff = c.fastForward(unification) ?: return sequenceOf()
            return if (ff.full()) {
                logger.count("Successful fast forward for $seedCandidate")
                sequenceOf(ff)
            } else sequenceOf()
        }

        if (sizeBound == 0) {
            logger.log("Trying ff on $c")
            logger.count("Hit size bound under $seedCandidate")
            logger.count("Trying ff for $seedCandidate")
            val ff = c.fastForward(unification) ?: return sequenceOf()
            return if (ff.full()) {
                logger.count("Successful fast forward for $seedCandidate")
                sequenceOf(ff)
            } else sequenceOf()
        }

        return fill(c, unification, sizeBound <= 1).flatMap { (newCand, cost) ->
            if (newCand.depth() > hardDepthBound) emptySequence()
            else {
                // TODO spawnAndRefine is slow for eager unification since we make a duplicate candidate.
                //      but making a new unification is slow for other unifs.
                val u = unification(newCand, query.posExsBeforeSubexprs)
                if (u.ok()) {
                    if (newCand.satisfiesDependencies()) {  // TODO ablate this
                        commitPriority(newCand, u, sizeBound - cost, hardDepthBound)
                    } else emptySequence()
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
