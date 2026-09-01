package util

import org.junit.jupiter.api.Test
import org.junit.jupiter.api.assertThrows
import testutil.OCamlExpr
import testutil.OCamlExpr.*
import testutil.parseOCamlExpr
import kotlin.test.assertEquals

class OCamlExprParserTest {

    private fun v(name: String) = Var(name)
    private fun app(f: OCamlExpr, vararg args: OCamlExpr) = args.fold(f) { acc, a -> App(acc, a) }
    private fun lam(vararg params: String, body: OCamlExpr) = Lam(params.toList(), body)

    @Test
    fun `app helper makes sense`() {
        assertEquals(App(App(Var("a"), Var("b")), Var("c")), app(v("a"), v("b"), v("c")))
        assertEquals(App(Var("a"), App(Var("b"), Var("c"))), app(v("a"), app(v("b"), v("c"))))
    }

    // --- Variables ---

    @Test
    fun `single identifier`() {
        assertEquals(v("x"), parseOCamlExpr("x"))
    }

    @Test
    fun `identifier with primes`() {
        assertEquals(v("x'"), parseOCamlExpr("x'"))
    }

    @Test
    fun `identifier with underscore and digits`() {
        assertEquals(v("my_var2"), parseOCamlExpr("my_var2"))
    }

    // --- Parenthesized operators ---

    @Test
    fun `plus operator`() {
        assertEquals(v("(+)"), parseOCamlExpr("(+)"))
    }

    @Test
    fun `minus operator`() {
        assertEquals(v("(-)"), parseOCamlExpr("(-)"))
    }

    @Test
    fun `less-than-or-equal operator`() {
        assertEquals(v("(<=)"), parseOCamlExpr("(<=)"))
    }

    @Test
    fun `pipe operator`() {
        assertEquals(v("(|>)"), parseOCamlExpr("(|>)"))
    }

    @Test
    fun `compose operator`() {
        assertEquals(v("(@@)"), parseOCamlExpr("(@@)"))
    }

    // --- Function application ---

    @Test
    fun `apply function to one argument`() {
        assertEquals(app(v("f"), v("x")), parseOCamlExpr("f x"))
    }

    @Test
    fun `apply function to two arguments`() {
        assertEquals(app(v("f"), v("x"), v("y")), parseOCamlExpr("f x y"))
    }

    @Test
    fun `apply function to three arguments`() {
        assertEquals(app(v("f"), v("x"), v("y"), v("z")), parseOCamlExpr("f x y z"))
    }

    @Test
    fun `application is left-associative`() {
        // f x y z  ==  ((f x) y) z
        val expected = App(App(App(v("f"), v("x")), v("y")), v("z"))
        assertEquals(expected, parseOCamlExpr("f x y z"))
    }

    @Test
    fun `apply operator to two arguments`() {
        assertEquals(app(v("(+)"), v("x"), v("y")), parseOCamlExpr("(+) x y"))
    }

    @Test
    fun `apply operator as prefix function`() {
        assertEquals(app(v("(*)"), v("a"), v("b")), parseOCamlExpr("(*) a b"))
    }

    // --- Lambda expressions ---

    @Test
    fun `lambda with one parameter`() {
        assertEquals(lam("x", body = v("x")), parseOCamlExpr("fun x -> x"))
    }

    @Test
    fun `lambda with two parameters`() {
        assertEquals(lam("x", "y", body = v("x")), parseOCamlExpr("fun x y -> x"))
    }

    @Test
    fun `lambda with three parameters`() {
        assertEquals(lam("x", "y", "z", body = v("x")), parseOCamlExpr("fun x y z -> x"))
    }

    @Test
    fun `lambda body is an application`() {
        assertEquals(
            lam("x", body = app(v("f"), v("x"))),
            parseOCamlExpr("fun x -> f x")
        )
    }

    @Test
    fun `lambda body uses multiple params in application`() {
        assertEquals(
            lam("x", "y", body = app(v("(+)"), v("x"), v("y"))),
            parseOCamlExpr("fun x y -> (+) x y")
        )
    }

    @Test
    fun `lambda body is another lambda`() {
        // fun x -> fun y -> x   is parsed as   fun x -> (fun y -> x)
        val expected = lam("x", body = lam("y", body = v("x")))
        assertEquals(expected, parseOCamlExpr("fun x -> fun y -> x"))
    }

    @Test
    fun `arrow is right-associative via lambda nesting`() {
        val inner = lam("y", body = v("y"))
        val expected = lam("x", body = inner)
        assertEquals(expected, parseOCamlExpr("fun x -> fun y -> y"))
    }

    // --- Parentheses for grouping ---

    @Test
    fun `redundant parens around variable`() {
        assertEquals(v("x"), parseOCamlExpr("(x)"))
    }

    @Test
    fun `double redundant parens`() {
        assertEquals(v("x"), parseOCamlExpr("((x))"))
    }

    @Test
    fun `parens group application argument`() {
        // f (g x)  — apply f to the result of (g x)
        val expected = App(v("f"), App(v("g"), v("x")))
        assertEquals(expected, parseOCamlExpr("f (g x)"))
    }

    @Test
    fun `parens change associativity of application`() {
        // f (g x) y  vs  f g x y — different trees
        val withParens = App(App(v("f"), App(v("g"), v("x"))), v("y"))
        assertEquals(withParens, parseOCamlExpr("f (g x) y"))
    }

    @Test
    fun `nested parens around application`() {
        assertEquals(App(v("f"), v("x")), parseOCamlExpr("((f x))"))
    }

    // --- Lambdas passed as arguments ---

    @Test
    fun `lambda passed as argument to function`() {
        // map (fun x -> x) xs
        val lam = lam("x", body = v("x"))
        val expected = App(App(v("map"), lam), v("xs"))
        assertEquals(expected, parseOCamlExpr("map (fun x -> x) xs"))
    }

    @Test
    fun `lambda with two params passed as argument`() {
        val lam = lam("x", "y", body = app(v("(+)"), v("x"), v("y")))
        val expected = App(v("fold"), lam)
        assertEquals(expected, parseOCamlExpr("fold (fun x y -> (+) x y)"))
    }

    @Test
    fun `operator passed as argument`() {
        // map (+) xs
        val expected = App(App(v("map"), v("(+)")), v("xs"))
        assertEquals(expected, parseOCamlExpr("map (+) xs"))
    }

    // --- Applying a lambda immediately ---

    @Test
    fun `immediately applied lambda`() {
        // (fun x -> x) y
        val expected = App(lam("x", body = v("x")), v("y"))
        assertEquals(expected, parseOCamlExpr("(fun x -> x) y"))
    }

    @Test
    fun `immediately applied lambda with multiple args`() {
        // (fun x y -> x) a b
        val expected = App(App(lam("x", "y", body = v("x")), v("a")), v("b"))
        assertEquals(expected, parseOCamlExpr("(fun x y -> x) a b"))
    }

    @Test
    fun `immediately applied lambda in argument position`() {
        // f ((fun x -> x) y)
        val expected = App(v("f"), App(lam("x", body = v("x")), v("y")))
        assertEquals(expected, parseOCamlExpr("f ((fun x -> x) y)"))
    }

    // --- Whitespace handling ---

    @Test
    fun `extra whitespace between tokens`() {
        assertEquals(App(v("f"), v("x")), parseOCamlExpr("f    x"))
    }

    @Test
    fun `newlines and tabs between tokens`() {
        assertEquals(App(v("f"), v("x")), parseOCamlExpr("f\n\tx"))
    }

    // --- Error cases ---

    @Test
    fun `empty input fails`() {
        assertThrows<IllegalArgumentException> { parseOCamlExpr("") }
    }

    @Test
    fun `unmatched paren fails`() {
        assertThrows<IllegalArgumentException> { parseOCamlExpr("(f x") }
    }

    @Test
    fun `lambda with no params fails`() {
        assertThrows<IllegalArgumentException> { parseOCamlExpr("fun -> x") }
    }

    @Test
    fun `bare arrow fails`() {
        assertThrows<IllegalArgumentException> { parseOCamlExpr("->") }
    }
}
