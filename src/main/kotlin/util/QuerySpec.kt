package util

import query.Query

data class QuerySpec(val name: String, val query: Query, val oracle: Oracle) {
    fun pair(): Pair<Query, Oracle> = query to oracle
}
