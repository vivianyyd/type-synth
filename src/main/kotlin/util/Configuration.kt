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
    val bound: Bound
) : Config {
    override fun toString(): String =
        listOf(test.name, "Running CVC: $runCVC", enumeratorTag, unificationTag, "Bound: $bound").joinToString(
            separator = "\n",
            postfix = "\n=====\n"
        )
}

data class Bound(val b: Int, val type: BoundTag)

enum class BoundTag {
    Depth, Choice
}
