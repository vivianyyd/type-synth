package test

import query.Query
import query.parseApp
import query.parseExamples
import util.ScrappyNewOracle

object WeirdTest {
    // f:. f id 0 is valid, but f_swap 0 id is not.
    val examples = mapOf(
        "(+ f)" to "(a -> a) -> a -> a",
        // TODO none of these examples show applying f to a *function* with wrong type
        "(+ (f inc n))" to "int",
        "(+ (f id n))" to "int",
        "(+ (f id id))" to "a -> a",
        "(+ (f id inc))" to "int -> int",
        "(+ (f id f))" to "(a -> a) -> a -> a",
        "(+ inc)" to "int -> int",
        "(+ id)" to "a -> a",
        "(+ n)" to "int",
        "(+ (inc n))" to "int",
        "(+ (inc (inc n)))" to "int",
        "(+ (id inc))" to "int -> int",
        "(+ (id n))" to "int",
        "(+ (id (inc n)))" to "int", // not necessary
        "(- (inc id))" to null,
        "(+ ((id inc) n))" to "int",
        "(+ (inc (id n)))" to "int",
    )

    val query: Query = parseExamples(examples.keys)
    val oracle = ScrappyNewOracle(examples.mapKeys { parseApp(it.key) })
}
