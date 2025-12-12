package test

import query.Query
import query.parseApp
import query.parseExamples
import util.ScrappyNewOracle

object HOFTest : Test {
    override val name = "HOFs"

    /*
     f: a -> b
     g: (a -> b) -> c
     h: ((a -> b) -> c) -> d
     */
    val examples = mapOf(
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

    override val query: Query = parseExamples(examples.keys)
    override val oracle = ScrappyNewOracle(examples.mapKeys { parseApp(it.key) })
}
