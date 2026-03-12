package query

import util.CheckingGroundTruthOracle
import util.Oracle

abstract class AbstractQuery {
    abstract val examples: Examples
    abstract val oracle: Oracle

    fun pair(): Pair<Examples, Oracle> = examples to oracle
}

class Query(override val examples: Examples, override val oracle: CheckingGroundTruthOracle) :
    AbstractQuery()
