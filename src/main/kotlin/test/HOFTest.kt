package test

import util.Query
import util.ScrappyNewOracle
import util.parseNewApp
import util.parseNewExamples

object HOFTest {
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

    val query: Query = parseNewExamples(examples.keys)
    val oracle = ScrappyNewOracle(examples.mapKeys { parseNewApp(it.key) })
}
