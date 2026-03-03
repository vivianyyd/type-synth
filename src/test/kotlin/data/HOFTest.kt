package data

import query.AbstractQuery
import query.Examples
import util.ScrappyNewOracle
import util.io.signedExample
import util.io.signedExamplesFromStrings

object HOFTest : AbstractQuery() {
    override val name = "HOFs"

    /*
    f: a -> b
    g: (a -> b) -> c
    h: ((a -> b) -> c) -> d
    */
    private val exs =
        mapOf(
            "(+ f)" to "a to b",
            "(+ g)" to "(a -> b) -> c",
            "(+ h)" to "((a -> b) -> c) -> d",
            "(+ a)" to "a",
            "(+ (f a))" to "b",
            "(+ (g f))" to "c",
            "(+ (h g))" to "d",
            "(- (h f))" to null,
            "(- (g a))" to null,
        )

    override val examples: Examples = signedExamplesFromStrings(exs.keys)
    override val oracle = ScrappyNewOracle(exs.mapKeys { signedExample(it.key) })
}
