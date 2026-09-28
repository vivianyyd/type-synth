package oneast.unit

import oneast.*
import org.junit.jupiter.api.Test
import query.App
import query.Example
import query.Name
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

/**
 * A program type-checks under every filling of a state's holes exactly when it type-checks under
 * the skolemized state. Checking against the holes themselves is not enough.
 */
class SkolemizationTest {
    private val I = 0
    private val B = 1
    private val L = 2
    private val labelArities = mapOf(I to 0, B to 0, L to 1)

    private fun int() = NamedLabel(I, listOf())
    private fun bool() = NamedLabel(B, listOf())
    private fun list(t: Type) = NamedLabel(L, listOf(t))
    private fun fn(from: Type, to: Type) = Arrow(from, to)
    private val a = Variable(0)

    private fun state(vararg context: Pair<String, Type>) =
        SearchState(
            names = context.withIndex().associate { it.value.first to it.index },
            types = context.map { it.second },
            labelArities = labelArities
        )

    /** cons : a -> L[a] -> [consResult], with enough around it to compare two lists. */
    private fun consWhoseResultIs(consResult: Type) =
        state(
            "cons" to fn(a, fn(list(a), consResult)),
            "compare" to fn(a, fn(a, int())),
            "nil" to list(a),
            "zero" to int(),
            "one" to int(),
            "tt" to bool(),
        )

    private fun app(f: String, vararg args: Example): Example =
        args.fold(Name(f) as Example) { acc, arg -> App(acc, arg) }

    /** compare (cons zero nil) (cons tt nil) */
    private val bad = app("compare", app("cons", Name("zero"), Name("nil")), app("cons", Name("tt"), Name("nil")))

    /** compare (cons zero nil) (cons one nil) */
    private val good = app("compare", app("cons", Name("zero"), Name("nil")), app("cons", Name("one"), Name("nil")))

    private fun ok(s: SearchState, ex: Example) = OneUnification(s, listOf(ex)).ok

    @Test
    fun `a hole becomes a fresh label applied to its type's variables`() {
        val hole = TypeHole()
        val skolemized = consWhoseResultIs(hole).skolemize().typeOf("cons")
        val k = ((skolemized as Arrow).r as Arrow).r as NamedLabel
        assertEquals(listOf<Type>(a), k.params)
        assertTrue(k.label !in labelArities)
        assertEquals(fn(a, fn(list(a), k)), skolemized)
    }

    /** The table in the overview: the same run, differing only in what cons returns. */
    @Test
    fun `a program that checks against the hole but not under every filling`() {
        val holes = consWhoseResultIs(TypeHole())
        assertTrue(ok(holes, bad), "Against the hole, the two results are unrelated variables")
        assertFalse(ok(holes.skolemize(), bad))
        // The filling that witnesses it,
        assertFalse(ok(consWhoseResultIs(list(a)), bad))
        // though not every filling does.
        assertTrue(ok(consWhoseResultIs(int()), bad))
    }

    @Test
    fun `a program that checks under every filling`() {
        val holes = consWhoseResultIs(TypeHole())
        assertTrue(ok(holes.skolemize(), good))
        for (filling in listOf(list(a), int(), a, fn(a, a), list(list(a))))
            assertTrue(ok(consWhoseResultIs(filling), good), "Filled with $filling")
    }

    /** The failure need not be a label clash: here it is the occurs check. */
    @Test
    fun `a program that some filling makes infinite`() {
        // apply : (a -> a) -> Int, and wrap : a -> [wrapResult]; so `apply wrap` needs
        // wrapResult = a.
        fun wrapWhoseResultIs(wrapResult: Type) =
            state("apply" to fn(fn(a, a), int()), "wrap" to fn(a, wrapResult))
        val program = app("apply", Name("wrap"))

        val holes = wrapWhoseResultIs(TypeHole())
        assertTrue(ok(holes, program))
        assertFalse(ok(holes.skolemize(), program))
        assertFalse(ok(wrapWhoseResultIs(list(a)), program), "L[a] = a is an infinite type")
    }

    @Test
    fun `one check can try many examples without them interfering`() {
        val holes = consWhoseResultIs(TypeHole()).skolemize()
        val check = OneUnification(holes, emptyList())
        for (ex in listOf(bad, good, bad, Name("cons"), good))
            assertEquals(ok(holes, ex), check.typeChecks(ex), "$ex")
        assertTrue(check.ok)
    }

    @Test
    fun `a state without holes is its own hardest filling`() {
        val filled = consWhoseResultIs(list(a))
        assertEquals(filled.types, filled.skolemize().types)
        assertEquals(ok(filled, good), ok(filled.skolemize(), good))
        assertEquals(ok(filled, bad), ok(filled.skolemize(), bad))
    }
}
