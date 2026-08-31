package oneast.searchstrategies

import oneast.SearchState
import oneast.Unification
import query.Examples

abstract class SearchStrategy(protected val examples: Examples) {
    /**
     * Lazily produces refinements of the seed [c] that pass [examples]. Output states are not
     * guaranteed to be concrete, but they are as concretized as this SearchStrategy will allow
     */
    abstract fun candidates(c: SearchState): Sequence<SearchState>

    protected fun posUnification(s: SearchState) = Unification(examples.programs(s.names).pos, s)

    protected fun failsNegexWithNoHoleConstraints(s: SearchState) =
        examples.programs(s.names).neg.any { Unification(it, s).passedWithNoConstraints }
}
