package oneast.searchstrategies

import oneast.OneUnification
import oneast.SearchState
import oneast.skolemize
import query.Examples

abstract class SearchStrategy(private val examples: Examples) {
    /**
     * Lazily produces refinements of the seed [c] that pass [examples]. Output states are not
     * guaranteed to be concrete, but they are as concretized as this SearchStrategy will allow
     */
    abstract fun candidates(c: SearchState): Sequence<SearchState>

    protected fun posUnification(s: SearchState) = OneUnification(s, examples.posNoSubexprs)

    /**
     * Whether some negative example type-checks however [s]'s holes are filled, so that no filling
     * of [s] can be a solution.
     */
    protected fun acceptsANegative(s: SearchState): Boolean {
        if (examples.neg.isEmpty()) return false
        val hardest = s.skolemize()
        return examples.neg.any { OneUnification(hardest, listOf(it)).ok }
    }
}
