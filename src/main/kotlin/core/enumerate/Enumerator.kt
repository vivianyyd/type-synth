package core.enumerate

import core.Candidate
import core.Language
import core.UnificationForCandidate
import core.enumerate.EnumeratorTag.*
import query.Query
import util.Bound
import util.Logger

sealed interface Enumerator<L : Language> {
    val seedCandidate: Candidate<L>
    fun enumerate(bound: Bound): List<Candidate<L>>
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
    bound: Bound,
    iterative: Boolean,
    logger: Logger
): List<Candidate<L>> {
    return if (iterative) {
        val sols = mutableListOf<Candidate<L>>()
        for (i in 1..bound.b) {
            logger.start("Depth $i")
            val currSols = enumerators.flatMap { it.enumerate(bound.copy(b = i)) }.toList()
            if (currSols.isNotEmpty()) {
                sols.addAll(currSols)
                break
            }
            logger.stop("Depth $i")
        }
        sols
    } else enumerators.flatMap { it.enumerate(bound) }
}
