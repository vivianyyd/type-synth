package test

import query.Query
import util.EqualityNewOracle

interface Test {
    val name: String
    val query: Query
    val oracle: EqualityNewOracle
    fun pair(): Pair<Query, EqualityNewOracle> = query to oracle
}

class TestPair(override val name: String, override val query: Query, override val oracle: EqualityNewOracle) : Test
