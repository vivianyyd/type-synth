package query

import org.junit.jupiter.api.Test
import org.junit.jupiter.api.assertThrows
import testutil.unsignedExample
import kotlin.test.assertEquals
import kotlin.test.assertNotEquals
import kotlin.test.assertNull

class ExampleTest {
    private val f = Name("f")
    private val g = Name("g")
    private val x = Name("x")
    private val y = Name("y")

    // ---------------------------------------------------------------- parsing

    @Test
    fun `parses a lambda whose body is an application`() {
        assertEquals(Lam("x", App(f, x)), unsignedExample("(fun x -> f x)"))
    }

    @Test
    fun `parses a lambda with several parameters as nested lambdas`() {
        assertEquals(Lam("x", Lam("y", App(App(f, x), y))), unsignedExample("(fun x y -> f x y)"))
    }

    @Test
    fun `parses a let`() {
        assertEquals(Let("y", App(f, x), App(g, y)), unsignedExample("(let y = f x in g y)"))
    }

    @Test
    fun `parses a lambda as an argument`() {
        assertEquals(App(f, Lam("x", x)), unsignedExample("(f (fun x -> x))"))
    }

    @Test
    fun `parses a line from the OCaml examples`() {
        val ex = unsignedExample("(List.filter (fun x2 -> ((=) x2 Num)) (List.cons Num Nil))")
        val pred = Lam("x2", App(App(Name("(=)"), Name("x2")), Name("Num")))
        val list = App(App(Name("List.cons"), Name("Num")), Name("Nil"))
        assertEquals(App(App(Name("List.filter"), pred), list), ex)
    }

    @Test
    fun `rejects a lambda that is not in a list of its own`() {
        assertThrows<IllegalArgumentException> { unsignedExample("(f fun x -> x)") }
    }

    @Test
    fun `rejects malformed binders`() {
        assertThrows<IllegalArgumentException> { unsignedExample("(fun -> x)") }
        assertThrows<IllegalArgumentException> { unsignedExample("(fun x ->)") }
        assertThrows<IllegalArgumentException> { unsignedExample("(fun (x) -> x)") }
        assertThrows<IllegalArgumentException> { unsignedExample("(let x = in x)") }
        assertThrows<IllegalArgumentException> { unsignedExample("(let x f in x)") }
    }

    @Test
    fun `binders are OCaml variable names`() {
        assertEquals(Lam("x'", Name("x'")), unsignedExample("(fun x' -> x')"))
        assertEquals(Lam("_", f), unsignedExample("(fun _ -> f)"))
        assertEquals(Lam("_acc1", f), unsignedExample("(fun _acc1 -> f)"))
        // Capitalized names are constructors, so OCaml would read these as patterns
        assertThrows<IllegalArgumentException> { unsignedExample("(fun Some -> x)") }
        assertThrows<IllegalArgumentException> { unsignedExample("(let Num = x in f)") }
        assertThrows<IllegalArgumentException> { unsignedExample("(fun match -> x)") }
        assertThrows<IllegalArgumentException> { unsignedExample("(fun 1x -> x)") }
        assertThrows<IllegalArgumentException> { unsignedExample("(fun (+) -> x)") }
        assertThrows<IllegalArgumentException> { unsignedExample("(fun _ -> _)") }
    }

    // ---------------------------------------------------------------- names

    @Test
    fun `names are the free names`() {
        assertEquals(setOf("f"), unsignedExample("(fun x -> f x)").names)
        assertEquals(setOf("f", "x", "g"), unsignedExample("(let y = f x in g y)").names)
    }

    @Test
    fun `a binder shadows a component of the same name`() {
        assertEquals(emptySet(), unsignedExample("(fun f -> f)").names)
        // The let's value is outside the scope of its name
        assertEquals(setOf("f"), unsignedExample("(let f = f in f)").names)
    }

    // ---------------------------------------------------------------- subexpressions

    @Test
    fun `subexpressions leave out those using a bound name`() {
        val ex = unsignedExample("(g (fun x -> f x y))")
        assertEquals(
            listOf(g, f, y, unsignedExample("(fun x -> f x y)"), ex),
            ex.subexprs()
        )
    }

    @Test
    fun `subexpressions of a let include its value but not uses of its name`() {
        val ex = unsignedExample("(let y = f x in g y)")
        assertEquals(listOf(f, x, App(f, x), g, ex), ex.subexprs())
    }

    @Test
    fun `examples drops positives that are subexpressions of others`() {
        val lam = unsignedExample("(fun x -> f x)")
        val ex = App(g, lam)
        assertEquals(listOf(ex), Examples(listOf(lam, ex, f), emptyList()).posNoSubexprs)
    }

    // ---------------------------------------------------------------- flattening

    @Test
    fun `flattening keeps a lambda argument whole`() {
        val lam = Lam("x", x)
        assertEquals(FlatApp("f", listOf(lam, y)), App(App(f, lam), y).flatten())
        assertEquals(App(App(f, lam), y), FlatApp("f", listOf(lam, y)).unflatten())
    }

    @Test
    fun `an application of a lambda or let does not flatten`() {
        assertNull(App(Lam("x", x), y).flatten())
        assertNull(Let("x", y, x).flatten())
    }

    @Test
    fun `examples that do not flatten are left out of the flat examples`() {
        val examples = Examples(listOf(App(Lam("x", App(f, x)), y), App(f, y)), emptyList())
        assertEquals(listOf(FlatApp("f"), FlatApp("f", listOf(y))), examples.flatPos("f"))
    }

    // ---------------------------------------------------------------- equality

    @Test
    fun `examples are equal up to renaming bound names`() {
        fun assertSame(a: String, b: String) {
            assertEquals(unsignedExample(a), unsignedExample(b))
            assertEquals(unsignedExample(a).hashCode(), unsignedExample(b).hashCode())
        }
        assertSame("(fun x -> f x)", "(fun y -> f y)")
        assertSame("(g (let a = f in a))", "(g (let b = f in b))")
        assertSame("(fun x y -> x)", "(fun a b -> a)")
        val examples = Examples(listOf(App(g, Lam("x", x)), App(g, Lam("y", y))), emptyList())
        assertEquals(1, examples.posNoSubexprs.size)
    }

    @Test
    fun `but not up to renaming free names, or which binder a name refers to`() {
        assertNotEquals(unsignedExample("(fun x -> f x)"), unsignedExample("(fun x -> g x)"))
        assertNotEquals(unsignedExample("(fun x -> f x)"), unsignedExample("(fun y -> f x)"))
        assertNotEquals(unsignedExample("(fun x y -> x)"), unsignedExample("(fun x y -> y)"))
    }

    // ---------------------------------------------------------------- inlining lets

    @Test
    fun `inlining puts each let's value where its name is used`() {
        assertEquals(
            unsignedExample("(pair (f x) (f x))"),
            unsignedExample("(let y = (f x) in (pair y y))").inlineLets()
        )
        assertEquals(
            unsignedExample("(cons Num Nil)"),
            unsignedExample("(let g = cons in (let h = g in (h Num Nil)))").inlineLets()
        )
        // An unused value is dropped
        assertEquals(g, unsignedExample("(let y = f in g)").inlineLets())
    }

    @Test
    fun `inlining does not let a binder capture the value's names`() {
        // The lambda's x is not the component x the value uses
        assertEquals(
            Lam("x1", App(App(Name("pair"), x), Name("x1"))),
            unsignedExample("(let y = x in (fun x -> pair y x))").inlineLets()
        )
        // A binder of the let's own name hides it
        assertEquals(
            unsignedExample("(pair f (fun y -> y))"),
            unsignedExample("(let y = f in (pair y (fun y -> y)))").inlineLets()
        )
    }

    @Test
    fun `positives are flat with their lets inlined`() {
        val examples = Examples(listOf(unsignedExample("(let g = f in (g x y))")), emptyList())
        assertEquals(listOf(FlatApp("f"), FlatApp("f", listOf(x, y))), examples.flatPos("f"))
    }

    // ---------------------------------------------------------------- printing

    @Test
    fun `prints as OCaml`() {
        assertEquals("f (fun x -> x) y", App(App(f, Lam("x", x)), y).toString())
        assertEquals("(fun x -> x) y", App(Lam("x", x), y).toString())
        assertEquals(
            "let y = f x in g (f y)", unsignedExample("(let y = f x in g (f y))").toString()
        )
        assertEquals("fun x -> fun y -> f x y", unsignedExample("(fun x y -> f x y)").toString())
    }

    @Test
    fun `depth and size count binders`() {
        val ex = unsignedExample("(f (fun x -> g x))")
        assertEquals(2, ex.depth())
        assertEquals(4, ex.size())
    }
}
