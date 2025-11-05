package core.enumerate

import core.Candidate
import core.Language

sealed interface Enumerator<L : Language> {
    fun enumerate(maxDepth: Int): List<Candidate<L>>
}