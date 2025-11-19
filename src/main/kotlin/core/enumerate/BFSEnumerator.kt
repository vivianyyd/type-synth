package core.enumerate

import core.Candidate
import core.Language
import core.UnificationForCandidate
import query.Query
import util.Bound

class BFSEnumerator<L : Language>(
    val query: Query,
    override val seedCandidate: Candidate<L>,
    private val unification: UnificationForCandidate<L>,
    private val mustPassNegatives: Boolean,
    private val minimizeSize: Boolean = false
) : Enumerator<L> {
    init {
        throw UnsupportedOperationException("No more BFS")
    }

    override fun enumerate(bound: Bound): List<Candidate<L>> =
        throw UnsupportedOperationException("No more BFS")
}
