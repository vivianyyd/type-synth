package util

import core.enumerate.EnumeratorTag
import core.unification.UnificationTag
import test.Test

interface Config

data class Configuration(
    val test: Test,
    val runCVC: Boolean,
    val enumeratorTag: EnumeratorTag,
    val unificationTag: UnificationTag,
    val finalRoundSketches: Boolean,
    val sizeBound: Int,
    val depthBound: Int
) : Config {
    override fun toString(): String =
        listOf(
            test.name,
            "Running CVC: $runCVC",
            enumeratorTag,
            unificationTag,
            "Size bound: $sizeBound",
            "Depth bound: $depthBound"
        )
            .joinToString(separator = "\n", postfix = "\n=====\n")
}

data class Bound(val b: Int, val type: BoundTag)

enum class BoundTag {
    Depth,
    Choice
}
