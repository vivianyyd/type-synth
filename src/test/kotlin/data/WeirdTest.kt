package data

import query.AbstractQuery
import query.Examples
import util.ScrappyNewOracle
import util.io.signedExample
import util.io.signedExamplesFromStrings

object WeirdTest : AbstractQuery() {
    override val name = "Weird"

    // f:. f id 0 is valid, but f_swap 0 id is not.
    private val exs =
        mapOf(
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

    override val examples: Examples = signedExamplesFromStrings(exs.keys)
    override val oracle = ScrappyNewOracle(exs.mapKeys { signedExample(it.key) })
}
