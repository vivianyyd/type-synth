package oneast.unit

import oneast.*
import org.junit.jupiter.api.Test
import query.App
import query.Example
import query.Name
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertNotEquals
import kotlin.test.assertNull
import kotlin.test.assertTrue

/**
 * Each use of a label-only blank unifies like a fresh variable, but the blank becomes one label.
 * So the examples can unify even when no choice of labels makes them type-check.
 */
class BlankAgreementTest {
    private val a = Variable(0)
    private val b = Variable(1)
    private val c = Variable(2)
    private val I = NamedLabel(0, listOf())
    private val B = NamedLabel(1, listOf())
    private val L = 2
    private val M = 3

    private fun state(vararg context: Pair<String, Type>): SearchState {
        val (names, types) = context.toList().unzip()
        return SearchState(names.withIndex().associate { it.value to it.index }, types, mapOf())
    }

    private fun app(fn: String, vararg args: Example): Example =
        args.fold(Name(fn) as Example) { f, arg -> App(f, arg) }

    private val pair = "pair" to Arrow(a, Arrow(b, I))

    /** `pair (f x) (g x)` */
    private val fxgx = app("pair", app("f", Name("x")), app("g", Name("x")))

    /** One use of x is unified with L and the other with M, but x is one label. */
    @Test
    fun `a blank is one label at every use`() {
        val s = state(pair, "x" to Blank(labelOnly = true), "f" to Arrow(NamedLabel(L, listOf()), I), "g" to Arrow(NamedLabel(M, listOf()), I))
        val u = OneUnification(s, listOf(fxgx))
        assertTrue(u.ok)
        assertFalse(u.satisfiable())
        assertEquals(setOf(L, M), u.badLabels())
    }

    /** A hole can become a type variable, which differs at each use. */
    @Test
    fun `a hole may be different at every use`() {
        val s = state(pair, "x" to TypeHole(), "f" to Arrow(NamedLabel(L, listOf()), I), "g" to Arrow(NamedLabel(M, listOf()), I))
        assertTrue(OneUnification(s, listOf(fxgx)).satisfiable())
    }

    /**
     * x is unified only with L, and y only with M, but `eq x y` forces x and y to be the same
     * label.
     */
    @Test
    fun `blanks that share a class must agree with each other`() {
        val s = state(
            "pair3" to Arrow(a, Arrow(b, Arrow(c, I))),
            "eq" to Arrow(a, Arrow(a, I)),
            "x" to Blank(labelOnly = true),
            "y" to Blank(labelOnly = true),
            "f" to Arrow(NamedLabel(L, listOf()), I),
            "g" to Arrow(NamedLabel(M, listOf()), I),
        )
        val example = app("pair3", app("eq", Name("x"), Name("y")), app("f", Name("x")), app("g", Name("y")))
        val u = OneUnification(s, listOf(example))
        assertTrue(u.ok)
        assertFalse(u.satisfiable())
        assertEquals(setOf(L, M), u.badLabels())
    }

    /** Only the label's name and arity must agree, not its arguments. */
    @Test
    fun `blanks agree on label and arity but not arguments`() {
        val x = "x" to Blank(labelOnly = true)
        val sameArity = state(pair, x, "f" to Arrow(NamedLabel(L, listOf(I)), I), "g" to Arrow(NamedLabel(L, listOf(B)), I))
        assertTrue(OneUnification(sameArity, listOf(fxgx)).satisfiable())

        val twoArities = state(pair, x, "f" to Arrow(NamedLabel(L, listOf(I)), I), "g" to Arrow(NamedLabel(L, listOf(I, I)), I))
        val u = OneUnification(twoArities, listOf(fxgx))
        assertTrue(u.ok)
        assertFalse(u.satisfiable())
        assertEquals(setOf(L), u.badLabels())
    }

    @Test
    fun `a blank is never a function`() {
        val s = state("x" to Blank(labelOnly = true), "f" to Arrow(Arrow(I, I), I))
        assertFalse(OneUnification(s, listOf(app("f", Name("x")))).satisfiable())
    }

    /**
     * `eq x y` puts x and y in one group, and `f x` requires that group to be L. z is used in no
     * example, so it is a group of its own with no required label.
     */
    @Test
    fun `blanks that share a class are grouped with the label they meet`() {
        val x = Blank(labelOnly = true)
        val y = Blank(labelOnly = true)
        val z = Blank(labelOnly = true)
        val s = state(pair, "eq" to Arrow(a, Arrow(a, I)), "x" to x, "y" to y, "z" to z, "f" to Arrow(NamedLabel(L, listOf()), I))
        val groups = OneUnification(s, listOf(app("pair", app("eq", Name("x"), Name("y")), app("f", Name("x"))))).blankGroups()!!
        assertEquals(groups.groupOf(x), groups.groupOf(y))
        assertEquals(L, groups.labelOf(groups.groupOf(y)))
        assertNotEquals(groups.groupOf(x), groups.groupOf(z))
        assertNull(groups.labelOf(groups.groupOf(z)))

        val clash = state(pair, "x" to x, "f" to Arrow(NamedLabel(L, listOf()), I), "g" to Arrow(NamedLabel(M, listOf()), I))
        assertNull(OneUnification(clash, listOf(fxgx)).blankGroups())
    }

    /** Filling a hole can make blanks disagree, and rewinding the filling undoes that. */
    @Test
    fun `refining a hole checks the blanks`() {
        val hole = TypeHole()
        val s = state(pair, "x" to Blank(labelOnly = true), "f" to Arrow(NamedLabel(L, listOf()), I), "g" to Arrow(hole, I))
        val u = OneUnification(s, listOf(fxgx))
        assertTrue(u.satisfiable())
        val mark = u.mark()
        assertTrue(u.refine(hole, NamedLabel(L, listOf())))
        u.rewindTo(mark)
        assertFalse(u.refine(hole, NamedLabel(M, listOf())))
        assertEquals(setOf(L, M), u.badLabels())
        u.rewindTo(mark)
        assertTrue(u.satisfiable())
    }
}
