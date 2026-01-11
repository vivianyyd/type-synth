package oneast

import query.Query
import util.Logger

/** Fills one hole at a time, in DFS priority order. */
class EnumerateOneAST(
    val query: Query,
    val seedSearchState: SearchState,
    private val mustPassNegatives: Boolean,
    private val logger: Logger,
) {
    /**
     * Fills one hole. Returns the resulting SearchState and the cost of that single commitment
     * made.
     */
    private fun fill(
        c: SearchState,
        unification: OneUnification,
        mustBeLeaf: Boolean
    ): Sequence<Pair<SearchState, Int>> {
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
                SearchState(
                    c.names, c.types.mapIndexed { i, p -> if (iToFill == i) newType else p }) to
                        cost
            }
    }

    private fun commitPriority(
        c: SearchState,
        unification: OneUnification,
        sizeBound: Int,
        hardDepthBound: Int
    ): Sequence<SearchState> {
        // if (c.toString().contains("put: L2")) logger.log("$c")
        if (c.full()) return sequenceOf(c)

        if (sizeBound == 0) {
            //            logger.log("Trying ff on $c")
            //            logger.count("Trying ff for $seedSearchState")
            val ff =
                c.fastForward { OneUnification(it, query.posNoSubexprs) } ?: return sequenceOf()
            //            logger.log("Got $ff")
            return if (ff.full()) {
                //                logger.log("Ff to $ff")
                //                logger.count("Successful fast forward for $seedSearchState")
                sequenceOf(ff)
            } else sequenceOf()
        }

        if (c.types.all { it.fillable().isEmpty() }) {
            return sequenceOf()
        }

        return fill(c, unification, sizeBound <= 1).flatMap { (newCand, cost) ->
            logger.count("Total candidates for $seedSearchState")
            if (newCand.depth() > hardDepthBound) emptySequence()
            else {
                //                logger.count("Calls to check for $seedSearchState")
                // TODO spawnAndRefine is slow for eager unification since we make a duplicate
                // candidate.
                //      but making a new unification is slow for other unifs.
                val u = OneUnification(newCand, query.posNoSubexprs)
                if (u.ok()) {
                    //                    if (newCand.satisfiesDependencies()) { // TODO ablate this
                    commitPriority(newCand, u, sizeBound - cost, hardDepthBound)
                    //                    } else emptySequence()
                } else emptySequence()
            }
        }
    }

    override fun enumerate(
        sketches: Boolean,
        sizeBound: Int,
        hardDepthBound: Int
    ): List<SearchState> {
        fun check(c: SearchState) =
            OneUnification(c, query.posNoSubexprs).ok() &&
                    (if (mustPassNegatives) query.neg.all { !OneUnification(c, listOf(it)).ok() }
                    else true)

        val seed =
            SearchState( // infer nullaries
                seedSearchState.names,
                seedSearchState.types.map { t ->
                    val commits: List<Pair<Hole, Blank>> =
                        when (t) {
                            is NArrow<*> -> listOf()
                            else -> t.listHoles().map { it to (it as ConcreteHole).blankExpansion }
                        }
                    commits.fold(t) { acc: SearchNode, commitment: Pair<Hole, Blank> ->
                        acc.replace(
                            commitment.first,
                            commitment.second as SearchNode
                        ) // TODO Extremely messy
                    }
                })
        // TODO bug: inferring nullaries can fail if there are multiple possible assignments of
        // variables to a nullary
        //      value. fix this later, solution is in notes
        return commitPriority(
            seed,
            OneUnification(seedSearchState, query.posNoSubexprs),
            sizeBound,
            hardDepthBound
        )
            .filter { c -> check(c) }
            .toList()
    }
}
