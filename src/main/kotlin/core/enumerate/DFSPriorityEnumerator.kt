package core.enumerate

import core.languages.*
import core.unification.Unification
import core.unification.UnificationForCandidate
import query.Query
import util.Logger

/** Fills one hole at a time, in DFS priority order. */
class DFSPriorityEnumerator<L : Language>(
    val query: Query,
    override val seedCandidate: Candidate<L>,
    private val unification: UnificationForCandidate<L>,
    private val mustPassNegatives: Boolean,
    private val logger: Logger,
) : Enumerator<L> {
    /**
     * Fills one hole. Returns the resulting Candidate and the cost of that single commitment made.
     */
    private fun fill(
        c: Candidate<L>,
        unification: Unification<L>,
        mustBeLeaf: Boolean
    ): Sequence<Pair<Candidate<L>, Int>> {
        val (iToFill, typeToFill) =
            c.types.withIndex().maxBy { (_, it) ->
                it.priority()
            } // todo want to order by hole depth, then remove bound on iterative deepening thing

        // New version doesn't use SearchNode-specified expansions for each node, only for the holes
        val holeToFill = typeToFill.fillable().maxBy { it.priority() }
        return holeToFill
            .expansions(unification, typeToFill.variableNames().size, mustBeLeaf)
            .asSequence()
            .map { holeFill -> typeToFill.replace(holeToFill, holeFill) to holeFill.costToCommit() }
            .map { (newType, cost) ->
                Candidate(
                    c.names, c.types.mapIndexed { i, p -> if (iToFill == i) newType else p }) to
                    cost
            }
    }

    private fun commitPriority(
        c: Candidate<L>,
        unification: Unification<L>,
        sizeBound: Int,
        hardDepthBound: Int
    ): Sequence<Candidate<L>> {
        //        logger.log("$c")
        if (c.full()) return sequenceOf(c)

        if (sizeBound == 0) {
            //            logger.log("Trying ff on $c")
            //            logger.count("Trying ff for $seedCandidate")
            val ff =
                c.fastForward { unification(it, query.posExsBeforeSubexprs) } ?: return sequenceOf()
            return if (ff.full()) {
                //                logger.log("Ff to $ff")
                //                logger.count("Successful fast forward for $seedCandidate")
                sequenceOf(ff)
            } else sequenceOf()
        }

        if (c.types.all { it.fillable().isEmpty() }) {
            return sequenceOf()
        }

        return fill(c, unification, sizeBound <= 1).flatMap { (newCand, cost) ->
            logger.count("Total candidates for $seedCandidate")
            if (newCand.depth() > hardDepthBound) emptySequence()
            else {
                //                logger.count("Calls to check for $seedCandidate")
                // TODO spawnAndRefine is slow for eager unification since we make a duplicate
                // candidate.
                //      but making a new unification is slow for other unifs.
                val u = unification(newCand, query.posExsBeforeSubexprs)
                if (u.ok()) {
                    if (newCand.satisfiesDependencies()) { // TODO ablate this
                        commitPriority(newCand, u, sizeBound - cost, hardDepthBound)
                    } else emptySequence()
                } else emptySequence()
            }
        }
    }

    override fun enumerate(
        sketches: Boolean,
        sizeBound: Int,
        hardDepthBound: Int
    ): List<Candidate<L>> {
        fun check(c: Candidate<L>) =
            unification(c, query.posExsBeforeSubexprs).ok() &&
                    (if (mustPassNegatives) query.negExamples.all { !unification(c, listOf(it)).ok() }
                    else true)

        val seed =
            Candidate( // infer nullaries
                seedCandidate.names,
                seedCandidate.types.map { t ->
                    val commits: List<Pair<Hole<L>, Blank>> =
                        when (t) {
                            is NArrow<*> -> listOf()
                            else -> t.listHoles().map { it to (it as ConcreteHole).blankExpansion }
                        }
                    commits.fold(t) { acc: SearchNode<L>, commitment: Pair<Hole<L>, Blank> ->
                        acc.replace(
                            commitment.first,
                            commitment.second as SearchNode<L>
                        ) // TODO Extremely messy
                    }
                })
        // TODO bug: inferring nullaries can fail if there are multiple possible assignments of
        // variables to a nullary
        //      value. fix this later, solution is in notes
        return commitPriority(
            seed,
            unification(seedCandidate, query.posExsBeforeSubexprs),
            sizeBound,
            hardDepthBound
        )
            .filter { c -> check(c) }
            .toList()
    }
}
