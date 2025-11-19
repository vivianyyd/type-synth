package util

import core.UnificationTag
import core.enumerate.EnumeratorTag
import test.Test

interface Config

data class Configuration(
    val test: Test,
    val runCVC: Boolean,
    val enumeratorTag: EnumeratorTag,
    val unificationTag: UnificationTag,
//    val bound: Bound,
    val maxDepth: Int
) : Config {
    override fun toString(): String =
        listOf(test.name, "Running CVC: $runCVC", enumeratorTag, unificationTag, "Max depth: $maxDepth").joinToString(
            separator = "\n",
            postfix = "\n=====\n"
        )
}

interface Bound
data class DepthBound(val b: Int) : Bound
data class ChoiceBound(val b: Int) : Bound
