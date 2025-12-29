package core.enumerate

import core.languages.*
import core.unification.Unification
import core.unification.UnificationForCandidate
import query.Query
import util.Logger
import util.partitions

/**
 * Partitions shallowest holes into named variables and label thunks, which are unified after
 * committing.
 */
class PartitionEnumerator<L : Language>(
    val query: Query,
    override val seedCandidate: Candidate<L>,
    private val unification: UnificationForCandidate<L>,
    private val mustPassNegatives: Boolean,
    private val logger: Logger,
) : Enumerator<L> {
    /** Deepens one type. */
    private fun fill(
        c: Candidate<L>,
        unification: Unification<L>,
        mustBeLeaf: Boolean
    ): Sequence<Pair<Candidate<L>, Int>> {
        /* For each partition, labels can be either empty or one of those partitions */
        val (iToFill, typeToFill) =
            c.types.withIndex().maxBy { (_, it) ->
                it.priority()
            } // todo want to order by hole depth, then remove bound on iterative deepening thing

        // New version doesn't use SearchNode-specified expansions for each node, only for the holes
        val holesToFill = typeToFill.fillable()
        // TODO it helps to refer to the hole's expansions since there may be additional constraints
        // on variables
        return partitions(holesToFill).flatMap { partition ->
            (0..partition.size).mapNotNull { i ->
                if (i == partition.size) { // no labels
                    TODO()
                } else { // set at index i is all labels
                    // first hole may have multiple variable expansions,
                    // ex. first hole in put: D[_, _] -> v0 -> v1 -> D[_, _] can be 0, 1, or 2
                    // we try all options for first hole
                    // then try all options for second hole subject to partition
                    // then all options for third hole subject to partition

                    TODO()
                }
            }
        }
        //        return holeToFill.expansions(unification, typeToFill.variableNames().size,
        // mustBeLeaf).asSequence()
        //            .map { holeFill -> typeToFill.replace(holeToFill, holeFill) to
        // holeFill.costToCommit() }
        //            .map { (newType, cost) ->
        //                Candidate(c.names, c.types.mapIndexed { i, p -> if (iToFill == i) newType
        // else p }) to cost
        //            }
    }

    private fun commitPriority(
        c: Candidate<L>,
        unification: Unification<L>,
        sizeBound: Int,
        hardDepthBound: Int
    ): Sequence<Candidate<L>> {
        if (c.full()) return sequenceOf(c)

        if (sizeBound == 0) {
            val ff = c.fastForward { unification(it, query.posNoSubexprs) } ?: return sequenceOf()
            return if (ff.full()) {
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
                // TODO spawnAndRefine is slow for eager unification since we make a duplicate
                // candidate.
                //      but making a new unification is slow for other unifs.
                val u = unification(newCand, query.posNoSubexprs)
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
            unification(c, query.posNoSubexprs).ok() &&
                    (if (mustPassNegatives) query.neg.all { !unification(c, listOf(it)).ok() }
                    else true)

        val seed =
            if (sketches) {
                Candidate(
                    seedCandidate.names,
                    seedCandidate.types.map { t ->
                        val commits: List<Pair<Hole<L>, Blank>> =
                            when (t) {
                                is NArrow<*> -> listOf()
                                else ->
                                    t.listHoles().map { it to (it as ConcreteHole).blankExpansion }
                            }
                        commits.fold(t) { acc: SearchNode<L>, commitment: Pair<Hole<L>, Blank> ->
                            acc.replace(
                                commitment.first,
                                commitment.second as SearchNode<L>
                            ) // TODO Extremely messy
                        }
                    })
                // TODO If no solution skipping nullaries with max size budget, we might need to try
                // one last time with
                //   no skipping. We need this if the nullary types contain variables which are not
                // the default variable
            } else seedCandidate
        return commitPriority(
            seed, unification(seedCandidate, query.posNoSubexprs), sizeBound, hardDepthBound
        )
            .filter { c -> check(c) }
            .toList()
    }
}
