package query

import util.Oracle

abstract class AbstractQuery {
    abstract val name: String
    abstract val examples: Examples
    abstract val oracle: Oracle

    fun pair(): Pair<Examples, Oracle> = examples to oracle
}

class Query(
    override val name: String,
    override val examples: Examples,
    override val oracle: Oracle
) : AbstractQuery()
