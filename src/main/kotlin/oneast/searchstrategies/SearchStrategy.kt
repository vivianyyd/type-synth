package oneast.searchstrategies

import oneast.OneUnification
import oneast.SearchState
import query.Examples

abstract class SearchStrategy(private val examples: Examples) {
    /**
     * Lazily produces refinements of the seed [c] that pass [examples]. Output states are not
     * guaranteed to be concrete, but they are as concretized as this SearchStrategy will allow
     */
    abstract fun candidates(c: SearchState): Sequence<SearchState>

    protected fun posUnification(s: SearchState) = OneUnification(s, examples.posNoSubexprs)

    protected fun failsNegexWithNoHoleConstraints(s: SearchState) =
        examples.neg.any { OneUnification(s, listOf(it)).passedWithNoConstraints }
}
