package fixtures

import query.Query
import util.Oracle
import util.QuerySpec

interface Test {
    val name: String
    val query: Query
    val oracle: Oracle

    fun pair(): Pair<Query, Oracle> = query to oracle

    fun toQuerySpec() = QuerySpec(name, query, oracle)
}

class TestPair(override val name: String, override val query: Query, override val oracle: Oracle) :
    Test
