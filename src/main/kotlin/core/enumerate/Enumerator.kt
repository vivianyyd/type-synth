package core.enumerate

import core.Candidate
import core.Language
import core.UnificationForCandidate
import core.enumerate.EnumeratorTag.*
import query.Query
import util.Logger

sealed interface Enumerator<L : Language> {
    val seedCandidate: Candidate<L>
    fun enumerate(maxDepth: Int): List<Candidate<L>>
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
