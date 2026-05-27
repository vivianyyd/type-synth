package query

import oneast.SearchState
import util.CheckingGroundTruthOracle
import util.Oracle

abstract class AbstractQuery {
    abstract val examples: Examples
    abstract val oracle: Oracle

    /**
     * A SearchState whose name → type assignments are taken as fixed when this query is solved.
     * Names in the seed are not enumerated again; their types and any associated label arities are
     * preserved through the search. Defaults to the empty state.
     */
    open val committedSeed: SearchState = SearchState.emptyState

    fun pair(): Pair<Examples, Oracle> = examples to oracle
}

class Query(
    override val examples: Examples,
    override val oracle: CheckingGroundTruthOracle,
    override val committedSeed: SearchState = SearchState.emptyState
) : AbstractQuery()
