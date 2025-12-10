package core.enumerate

import core.enumerate.EnumeratorTag.*
import core.languages.Candidate
import core.languages.Language
import core.unification.UnificationForCandidate
import query.Query
import util.Logger

sealed interface Enumerator<L : Language> {
    val seedCandidate: Candidate<L>
    fun enumerate(sketches: Boolean, sizeBound: Int, hardDepthBound: Int): List<Candidate<L>>
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
    enumerators: List<Enumerator<L>>,
    sketches: Boolean,
    sizeBound: Int,
    hardDepthBound: Int,
    fastForward: Boolean,
    iterative: Boolean,
    logger: Logger
): List<Candidate<L>> {
    val holes = enumerators.map { it.seedCandidate.holes }
    if (holes.min() > sizeBound) throw IllegalArgumentException("Size bound not large enough for any concrete types")

    return if (iterative) {
        val sols = mutableListOf<Candidate<L>>()
        for (depth in 2..hardDepthBound) {  // depth starts at 2 because outermost labels are 1
            logger.start("Depth $depth")
            for (size in 1..sizeBound) {
                logger.start("Size $size")
                val currSols = enumerators
                    .filter {
                        if (!fastForward) it.seedCandidate.holes <= size
                        else true
                    }
                    .flatMap { it.enumerate(sketches, size, depth) }
                    .toList()
                logger.stop("Size $size")
                if (currSols.isNotEmpty()) {
                    sols.addAll(currSols)
                    logger.log("STOPPED AT SIZE $size")
                    break
                }
            }
            logger.stop("Depth $depth")
            if (sols.isNotEmpty()) {
                logger.log("STOPPED AT DEPTH $depth")
                break
            }
        }
        sols
    } else enumerators.flatMap { it.enumerate(sketches, sizeBound, hardDepthBound) }
}
