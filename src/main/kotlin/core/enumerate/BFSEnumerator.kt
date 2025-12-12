package core.enumerate

import core.languages.Candidate
import core.languages.Language
import core.unification.UnificationForCandidate
import query.Query

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

    override fun enumerate(
        sketches: Boolean,
        sizeBound: Int,
        hardDepthBound: Int
    ): List<Candidate<L>> = throw UnsupportedOperationException("No more BFS")
}
