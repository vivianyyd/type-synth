package fixtures

import query.Query
import util.Oracle

interface Test {
    val name: String
    val query: Query
    val oracle: Oracle

    fun pair(): Pair<Query, Oracle> = query to oracle
}

class TestPair(override val name: String, override val query: Query, override val oracle: Oracle) :
    Test
