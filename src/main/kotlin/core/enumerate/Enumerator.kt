package core.enumerate

import core.Candidate
import core.Language
import core.UnificationForCandidate
import core.enumerate.EnumeratorTag.*
import query.Query
import util.Logger

sealed interface Enumerator<L : Language> {
    val seedCandidate: Candidate<L>
    fun enumerate(sizeBound: Int, hardDepthBound: Int): List<Candidate<L>>
}

enum class EnumeratorTag {
    BFS, DFSLeft, DFSPriority, Product
}

fun <L : Language> enumerator(
    tag: EnumeratorTag,
    query: Query,
    seedCandidate: Candidate<L>,
    unification: UnificationForCandidate<L>,
    mustPassNegatives: Boolean,
    logger: Logger
) = when (tag) {
    BFS -> error("BFS not supported yet")
    DFSLeft -> DFSLeftEnumerator(query, seedCandidate, unification, mustPassNegatives, logger)
    DFSPriority -> DFSPriorityEnumerator(query, seedCandidate, unification, mustPassNegatives, logger)
    Product -> error("Product enumeration not supported yet")
}

fun <L : Language> solutions(
    enumerators: List<Enumerator<L>>, sizeBound: Int, hardDepthBound: Int, iterative: Boolean, logger: Logger
): List<Candidate<L>> {
    val holes = enumerators.map { it.seedCandidate.holes }
    if (holes.min() > sizeBound) throw IllegalArgumentException("Size bound not large enough for any concrete types")

    return if (iterative) {
        val sols = mutableListOf<Candidate<L>>()
        for (depth in 1..hardDepthBound) {
            logger.start("Depth $depth")
            for (size in (holes.min() + depth - 1)..sizeBound) {
                logger.start("Size $size")
                val currSols =
                    enumerators.filter { it.seedCandidate.holes <= size }.flatMap { it.enumerate(size, depth) }
                        .toList()
                if (currSols.isNotEmpty()) {
                    sols.addAll(currSols)
                    break
                }
                logger.stop("Size $size")
            }
            logger.stop("Depth $depth")
        }
        sols
    } else enumerators.flatMap { it.enumerate(sizeBound, hardDepthBound) }
}
