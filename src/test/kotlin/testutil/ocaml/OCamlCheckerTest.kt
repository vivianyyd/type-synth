package testutil.ocaml

import org.junit.jupiter.api.Test
import query.App
import query.Lam
import query.Let
import query.Name
import testutil.unsignedExample
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class OCamlCheckerTest {
    private val unit = Name("()")
    private val x = Name("x")
    private val v = Name("v")

    @Test
    fun `a let's value becomes a lambda and each use an application to unit`() {
        assertEquals(
            Let("x", Lam("_", v), App(App(Name("f"), App(x, unit)), App(x, unit))),
            thunkLets(unsignedExample("(let x = v in f x x)"))
        )
        assertEquals("let x = fun _ -> v in f (x ()) (x ())", thunkLets(unsignedExample("(let x = v in f x x)")).toString())
    }

    @Test
    fun `a lambda parameter of the same name is not a use`() {
        assertEquals(
            Let("x", Lam("_", v), Lam("x", x)),
            thunkLets(unsignedExample("(let x = v in (fun x -> x))"))
        )
    }

    @Test
    fun `an inner let's value still sees the outer let`() {
        assertEquals(
            Let("x", Lam("_", v), Let("x", Lam("_", App(x, unit)), App(x, unit))),
            thunkLets(unsignedExample("(let x = v in (let x = x in x))"))
        )
    }

    @Test
    fun `examples without lets are unchanged`() {
        val ex = unsignedExample("(f (fun x -> g x) y)")
        assertEquals(ex, thunkLets(ex))
    }

    // These run ocamlc. `(fun a b -> b) p q` stands in for a pair, so q is the result.

    /** A let-bound non-value used at two types: Hindley-Milner accepts it, OCaml does not. */
    private val valueRestricted =
        unsignedExample(
            "(let f = (List.map (fun x -> x)) in ((fun a b -> b) (f (List.cons Num Nil)) (f (List.cons Str Nil))))"
        )

    @Test
    fun `ocamlc rejects a value-restricted let as written`() {
        assertFalse(OCamlChecker().valid(valueRestricted))
    }

    @Test
    fun `ocamlc accepts a value-restricted let when lets are thunked`() {
        assertTrue(OCamlChecker(thunkLets = true).valid(valueRestricted))
    }

    @Test
    fun `thunking lets keeps real type errors`() {
        val checker = OCamlChecker(thunkLets = true)
        assertFalse(checker.valid(unsignedExample("(let f = (List.map (fun x -> (+) x Num)) in (f (List.cons Str Nil)))")))
        // The value is checked even if the name is never used
        assertFalse(checker.valid(unsignedExample("(let x = ((+) Num Str) in Num)")))
    }

    // ---------------------------------------------------------------- labels

    private val labels = mapOf("f" to listOf(null, "l"))

    @Test
    fun `a labelled argument is written with its label`() {
        assertEquals("f x ~l:(g y)", withLabels(unsignedExample("(f x (g y))"), labels).toString())
        // Under-applied, so there is no argument to label
        assertEquals("f x", withLabels(unsignedExample("(f x)"), labels).toString())
        // Labels inside arguments too
        assertEquals("h (f x ~l:(y))", withLabels(unsignedExample("(h (f x y))"), labels).toString())
    }

    @Test
    fun `a binder of the same name is not the component`() {
        val ex = unsignedExample("(fun f -> f x y)")
        assertEquals(ex, withLabels(ex, labels))
    }

    @Test
    fun `ocamlc accepts a labelled component applied positionally in an example`() {
        val ex = unsignedExample("(Option.value (Option.some Num) Num)")
        assertTrue(OCamlChecker(labels = mapOf("Option.value" to listOf(null, "default"))).valid(ex))
        // Without the label, OCaml passes Num to Option.value's result instead
        assertFalse(OCamlChecker(labels = emptyMap()).valid(ex))
    }

    // ---------------------------------------------------------------- dummies

    @Test
    fun `dummy values replace whole names only`() {
        assertEquals(
            "String.length (String.make 1 'a')",
            OCamlChecker().source(unsignedExample("(String.length (String.make Num Char))"))
        )
    }
}
