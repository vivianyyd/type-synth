package oneast.unit

import oneast.*
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Test
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import query.App
import query.Example
import query.Name
import testutil.loadQueryFromFile
import testutil.parseSearchState
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertTrue

class UnificationTest {

    companion object {
        @JvmStatic
        fun oneBlankTwoLabels() =
            listOf(
                Arguments.of(
                    "dictput",
                    "Ebi=L0[., .] ; Eib=L0[., .] ; Eii=L0[., .] ; Num=L1[] ; put=L0[V0, V1] -> V0 -> V1 -> L0[V1, _] ; true=L2[]",
                    "put (put Eib Num true) Num true"
                ),
                Arguments.of(
                    "dictput",
                    "Ebi=L0[., .] ; Eib=L0[., .] ; Eii=L0[., .] ; Num=L1[] ; put=L0[V0, V1] -> V0 -> V1 -> L0[V1, _] ; true=L2[]",
                    "put (put Ebi true Num) true Num"
                ),
                Arguments.of(
                    "dictput",
                    "Ebi=L0[., .] ; Eib=L0[., .] ; Eii=L0[., .] ; Num=L1[] ; put=L0[V1, V0] -> V0 -> V1 -> L0[V0, _] ; true=L2[]",
                    "put (put Eib Num true) Num true"
                ),
                Arguments.of(
                    "dictput",
                    "Ebi=L0[., .] ; Eib=L0[., .] ; Eii=L0[., .] ; Num=L1[] ; put=L0[V1, V0] -> V0 -> V1 -> L0[V0, _] ; true=L2[]",
                    "put (put Ebi true Num) true Num"
                ),
                Arguments.of(
                    "dictput",
                    "Ebi=L0[., .] ; Eib=L0[., .] ; Eii=L0[., .] ; Num=L1[] ; put=L0[V1, V0] -> V0 -> V1 -> L0[V1, V1] ; true=L2[]",
                    "put (put Eib Num true) Num true"
                ),
                Arguments.of(
                    "dictput",
                    "Ebi=L0[., .] ; Eib=L0[., .] ; Eii=L0[., .] ; Num=L1[] ; put=L0[V1, V0] -> V0 -> V1 -> L0[V1, V1] ; true=L2[]",
                    "put (put Ebi true Num) true Num"
                ),
                Arguments.of(
                    "dictchain",
                    "b=L0[] ; chain=L1[V0, V0] -> L1[V0, V0] -> L1[V0, V0] ; dbb=L1[., .] ; dbi=L1[., .] ; dib=L1[., .] ; dii=L1[., .] ; i=L2[] ; put=L1[V0, V1] -> V0 -> V1 -> L1[_, _]",
                    "put (chain dib dbb) i b"
                ),
                Arguments.of(
                    "dictchain",
                    "b=L0[] ; chain=L1[V0, V1] -> L1[V1, V2] -> L1[V0, V0] ; dbb=L1[., .] ; dbi=L1[., .] ; dib=L1[., .] ; dii=L1[., .] ; i=L2[] ; put=L1[V0, V1] -> V0 -> V1 -> L1[_, _]",
                    "put (chain dib dbb) i b"
                ),
                Arguments.of(
                    "dictchain",
                    "b=L0[] ; chain=L1[V0, V0] -> L1[V0, V0] -> L1[V0, V0] ; dbb=L1[., .] ; dbi=L1[., .] ; dib=L1[., .] ; dii=L1[., .] ; i=L2[] ; put=L1[V1, V0] -> V0 -> V1 -> L1[_, _]",
                    "put (chain dib dbb) i b"
                ),
                Arguments.of(
                    "polymorphic-dictchain",
                    "({})=L0[.] ; b=L1[] ; chain=L0[V0] -> L0[V1] -> L0[V0] ; i=L2[] ; put=L0[V1] -> V0 -> V1 -> L0[V1]",
                    "put (chain (put ({}) i b) (put ({}) b i)) i i"
                ),
                Arguments.of(
                    "polymorphic-dictchain",
                    "({})=L0[.] ; b=L1[] ; chain=L0[V0] -> L0[V0] -> L0[V0] ; i=L2[] ; put=L0[V0] -> V0 -> V1 -> L0[V0]",
                    "chain (chain (put ({}) i b) (put ({}) b i))"
                ),
                Arguments.of(
                    "polymorphic-dictchain",
                    "({})=L0[.] ; b=L1[] ; chain=L0[V0] -> L0[V0] -> L0[V0] ; i=L2[] ; put=L0[V0] -> V0 -> V1 -> L0[V0]",
                    "chain (chain (put ({}) b i) (put ({}) i i))"
                ),
                Arguments.of(
                    "polymorphic-dictchain",
                    "({})=L0[.] ; b=L1[] ; chain=L0[V0] -> L0[V0] -> L0[V0] ; i=L2[] ; put=L0[V0] -> V0 -> V1 -> L0[V0]",
                    "chain (put ({}) b i) (put (put ({}) i i) i i)"
                ),
                Arguments.of(
                    "polymorphic-dictchain",
                    "({})=L0[.] ; b=L1[] ; chain=L0[V0] -> L0[V0] -> L0[V0] ; i=L2[] ; put=L0[V0] -> V0 -> V1 -> L0[V0]",
                    "chain (put ({}) i b) (put (put ({}) b b) b b)"
                ),
                Arguments.of(
                    "polymorphic-dictchain",
                    "({})=L0[.] ; b=L1[] ; chain=L0[V0] -> L0[V0] -> L0[V1] ; i=L2[] ; put=L0[V1] -> V0 -> V1 -> L0[V1]",
                    "chain (chain (put ({}) i b) (put ({}) b i))"
                ),
                Arguments.of(
                    "polymorphic-dictchain",
                    "({})=L0[.] ; b=L1[] ; chain=L0[V0] -> L0[V0] -> L0[V1] ; i=L2[] ; put=L0[V1] -> V0 -> V1 -> L0[V1]",
                    "put (chain (put ({}) i b) (put ({}) b i)) i i"
                ),
                Arguments.of(
                    "polymorphic-dictchain",
                    "({})=L0[.] ; b=L1[] ; chain=L0[V0] -> L0[V0] -> L0[V1] ; i=L2[] ; put=L0[V1] -> V0 -> V1 -> L0[V1]",
                    "chain (put ({}) i b) (chain (put ({}) b i) (put ({}) i b))"
                ),
            )
    }

    private val a = Variable(0)
    private val b = Variable(1)
    private val I = NamedLabel(0, listOf())
    private val B = NamedLabel(1, listOf())
    private val f = Name("f")
    private val g = Name("g")
    private val labelArities = mapOf(0 to 0, 1 to 0, 2 to 1, 3 to 2)

    private fun makeContext(context: List<Pair<String, Type>>): SearchState {
        val (names, types) = context.unzip()
        return SearchState(
            names = names.withIndex().associate { it.value to it.index },
            types = types,
            labelArities
        )
    }

    private fun makeContext(vararg context: Pair<String, Type>): SearchState =
        makeContext(context.toList())

    private fun ok(context: SearchState, program: Example) =
        OneUnification(context, listOf(program)).ok

    private fun assertOk(context: SearchState, program: Example) = assertTrue(ok(context, program))

    private fun assertFail(context: SearchState, program: Example) =
        assertFalse(ok(context, program))

    @Test
    fun `id inc`() {
        val examples = loadQueryFromFile("id-inc").examples
        // {id=_ -> V0, inc=_ -> _, n=.L} ought to pass the positive example
        // (id inc) n
        val context =
            makeContext(
                listOf(
                    "id" to Arrow(TypeHole(), a),
                    "inc" to Arrow(TypeHole(), TypeHole()),
                    "n" to Blank(labelOnly = true)
                )
            )
        examples.posNoSubexprs.forEach {
            assert(OneUnification(context, listOf(it)).ok) { "Bad positive example: $it" }
        }
    }

    @Test
    fun `functions with same variables`() {
        val ab = Arrow(a, b)
        val bai = Arrow(Arrow(b, a), Arrow(a, b))
        val context = makeContext("f" to bai, "g" to ab)
        assertOk(context, App(f, g))
        assertSameType(Arrow(b, a), OneUnification(context, emptyList()).type(App(f, g)))
    }

    @Test
    fun `int a int and a a int`() {
        val iai = Arrow(I, Arrow(a, I))
        val aai = Arrow(a, Arrow(a, I))
        val context1 = makeContext("f" to Arrow(iai, iai), "g" to aai)
        assertOk(context1, App(f, g))
        assertSameType(Arrow(I, Arrow(I, I)), OneUnification(context1, emptyList()).type(App(f, g)))

        val context2 = makeContext("f" to Arrow(aai, aai), "g" to iai)
        assertOk(context2, App(f, g))
        assertSameType(Arrow(I, Arrow(I, I)), OneUnification(context2, emptyList()).type(App(f, g)))
    }

    @Test
    fun `OCaml compare and max`() {
        /*
        compare: a -> a -> int
        max: a -> a -> a

        We do find
        {0=L0[], 1=L0[], compare=V0 -> V0 -> L0[], max=V0-> V0 -> V0, min=V0 -> V0 -> V0}
        but we add the counterexample ((compare) (max)) (compare)       Posex: true
         */
        val context =
            makeContext("compare" to Arrow(a, Arrow(a, I)), "max" to Arrow(a, Arrow(a, a)))
        val compare = Name("compare")
        val max = Name("max")
        val example = App(App(compare, max), compare)
        val unify = OneUnification(context, listOf(example))

        println(unify.type(App(compare, max)))
        println(unify.type(compare))

        assertSameType( // (V0 -> V0 -> V0) -> L0[]
            Arrow(Arrow(a, Arrow(a, a)), I), unify.type(App(compare, max))
        )
        assertSameType( // (V0 -> V0 -> L0[]) -> (V0 -> V0 -> L0[])
            Arrow(
                Arrow(a, Arrow(a, I)),
                Arrow(a, Arrow(a, I)),
            ),
            unify.type(App(max, compare))
        )

        assertTrue(unify.ok)
    }

    @Test
    fun `param and arg specialize - concrete in parameter`() {
        val context =
            makeContext(
                // f: ('a -> 'a -> Int) -> Int
                "f" to Arrow(Arrow(a, Arrow(a, I)), I),
                // g: 'b -> 'b -> 'b
                "g" to Arrow(a, Arrow(a, a))
            )

        val example = App(f, g)
        assertOk(context, example)
    }

    @Test
    fun `param and arg specialize - concrete in argument`() {
        val context =
            makeContext(
                // f: ('a -> 'a -> 'a) -> Int
                "f" to Arrow(Arrow(a, Arrow(a, a)), I),
                // g: 'b -> 'b -> Int
                "g" to Arrow(a, Arrow(a, I))
            )

        val example = App(f, g)
        assertOk(context, example)
    }

    @Test
    fun `big dictchain candidate`() {
        /*
        (chain dib) (chain dbi dii) with
            put=L0[L0[V0, V0], V0] -> V0 -> V1 -> V0
            dbb=L0[L0[V0, V0], V0]
            dbi=L0[L0[V0, V0], V0]
            dib=L0[L0[V0, V0], V0]
            dii=L0[L0[V0, V0], V0]
            chain=V0 -> V0 -> L0[V0, V0]
            i=L0[V0, V0]
            b=L0[V0, V0]
         */
        val laa = NamedLabel(3, listOf(a, a))
        val llaaa = NamedLabel(3, listOf(laa, a))
        val context =
            makeContext(
                "dbi" to llaaa,
                "dib" to llaaa,
                "dii" to llaaa,
                "put" to Arrow(llaaa, Arrow(a, Arrow(b, a))),
                "chain" to Arrow(a, Arrow(a, laa))
            )
        val chain = Name("chain")
        val cDib = App(chain, Name("dib"))
        val cDbiDii = App(App(chain, Name("dbi")), Name("dii"))
        val example = App(cDib, cDbiDii)

        val u = OneUnification(context, listOf(example))
        assertSameType(Arrow(llaaa, NamedLabel(3, listOf(llaaa, llaaa))), u.type(cDib))
        assertSameType(NamedLabel(3, listOf(llaaa, llaaa)), u.type(cDbiDii))
        // must unify:
        // L0[L0[V0, V0], V0]
        // L0[L0[L0[V0, V0], V0], L0[L0[V0, V0], V0]]

        // must unify:
        // L0[   V0,      V0],  V0
        // L0[L0[V0, V0], V0],  L0[L0[V0, V0], V0]

        // must unify:
        //    V0,       V0],  V0
        // L0[V0, V0],  V0],  L0[L0[V0, V0], V0]

        // TODO this fails by going through the occurs check; would that also happen in HM?
        assertFail(context, example)
    }

    @Test
    fun `bind variable to different things in different arguments`() {
        val aaa = Arrow(a, Arrow(a, a))
        val context = makeContext("f" to aaa, "x" to I, "y" to B)
        assertOk(context, App(f, Name("x")))
        assertFail(context, App(App(f, Name("x")), Name("y")))
    }

    @Test
    fun `bind variable to different things within one argument`() {
        val endodict = NamedLabel(3, params = listOf(a, a))
        val iiDict = NamedLabel(3, params = listOf(I, I))
        val ibDict = NamedLabel(3, params = listOf(I, B))
        val context = makeContext("f" to Arrow(endodict, I), "x" to iiDict, "y" to ibDict)
        assertOk(context, App(f, Name("x")))
        assertFail(context, App(f, Name("y")))
    }

    @Test
    fun `aba and int int int`() {
        val aba = Arrow(a, Arrow(b, a))
        val iii = Arrow(I, Arrow(I, I))
        val context1 = makeContext("f" to Arrow(aba, I), "g" to iii)
        assertOk(context1, App(f, g))

        val context2 = makeContext("f" to Arrow(iii, I), "g" to aba)
        assertOk(context2, App(f, g))
    }

    @Test
    fun `aba and a a int`() {
        val aba = Arrow(a, Arrow(b, a))
        val aai = Arrow(a, Arrow(a, I))
        val context1 = makeContext("f" to Arrow(aba, I), "g" to aai)
        assertOk(context1, App(f, g))

        val context2 = makeContext("f" to Arrow(aai, I), "g" to aba)
        assertOk(context2, App(f, g))
    }

    @Test
    fun `bind output`() {
        val aba = Arrow(a, Arrow(b, a))
        val aai = Arrow(a, Arrow(a, I))
        /*
        f: (a -> b -> a) -> a -> b -> a
        g: a -> a -> int
        After applying f g, both a and b should be bound to int
         */
        val context =
            makeContext("f" to Arrow(aba, Arrow(a, Arrow(b, a))), "g" to aai, "0" to I, "true" to B)
        val example = App(f, g)

        assertOk(context, example)
        val u = OneUnification(context, listOf(example))
        assertSameType(Arrow(I, Arrow(I, I)), u.type(example))

        assertOk(context, App(App(example, Name("0")), Name("0")))
        assertFail(context, App(example, Name("true")))
        assertFail(context, App(App(example, Name("0")), Name("true")))
    }

    @Test
    fun `aba and c int c`() {
        val aba = Arrow(a, Arrow(b, a))
        val bib = Arrow(b, Arrow(I, b))
        val context1 = makeContext("f" to Arrow(aba, I), "g" to bib)
        assertOk(context1, App(f, g))

        val context2 = makeContext("f" to Arrow(bib, I), "g" to aba)
        assertOk(context2, App(f, g))
    }

    @Test
    fun `parameter specializes to match argument`() {
        val context = makeContext("f" to Arrow(a, I), "x" to Arrow(B, I))
        val example = App(f, Name("x"))
        assertOk(context, example)
    }

    @Test
    fun `argument specializes to match parameter`() {
        val context = makeContext("f" to Arrow(Arrow(B, I), I), "g" to Arrow(a, I))
        val example = App(f, g)
        assertOk(context, example)
    }

    @Test
    fun `both types specialize to each other's concrete parts`() {
        val context = makeContext("f" to Arrow(a, I), "g" to Arrow(B, a))
        val example = App(f, g)
        assertOk(context, example)
    }

    @Test
    fun `fail to unify Int with function type`() {
        val context = makeContext("f" to Arrow(Arrow(a, b), I), "x" to I)
        val example = App(f, Name("x"))
        assertFail(context, example)
    }

    @Test
    fun `shared variable names don't clash due to unique instantiation ids`() {
        val context = makeContext("f" to Arrow(a, I), "g" to Arrow(Arrow(a, b), I))
        val example = App(g, f)
        assertOk(context, example)
    }

    @Test
    fun `fail to unify different type constructors`() {
        val context = makeContext("f" to Arrow(I, I), "x" to B)
        val example = App(f, Name("x"))
        assertFail(context, example)
    }

    /**
     * Negative test case: Type constructor parameter count mismatch. This test verifies that
     * OneUnification properly rejects types where a type constructor is used with the wrong number
     * of parameters relative to its declared arity.
     *
     * In this case, List is declared with arity 1, but 'x' attempts to use it with 2 parameters.
     * When trying to unify f's parameter (List with 1 param) with x (List with 2 params), the arity
     * mismatch should cause unification to fail.
     */
    @Test
    fun `fail to unify type constructors with different parameter counts`() {
        val context =
            makeContext(
                // f: List<Int> -> Int (List correctly used with 1 param)
                "f" to
                        Arrow(
                            NamedLabel(2, listOf(I)), // List<Int>
                            I // Int
                        ),
                // x: List<Int, Bool> (List incorrectly used with 2 params)
                "x" to NamedLabel(2, listOf(I, B))
            )

        val example = App(f, Name("x"))
        assertFail(context, example)
    }

    @Test
    fun `unify identity function with Int value`() {
        val context = makeContext("id" to Arrow(a, a), "x" to I)
        val example = App(Name("id"), Name("x"))
        assertOk(context, example)
    }

    @Test
    fun `specialization fails - incompatible concrete types`() {
        val context =
            makeContext(
                // f: Int -> Int
                "f" to Arrow(I, I),
                // g: Bool -> Bool
                "g" to Arrow(B, B)
            )

        val example = App(f, g)
        assertFail(context, example)
    }

    @Test
    fun `specialization fails - structure mismatch`() {
        val context = makeContext("f" to Arrow(Arrow(a, a), I), "x" to I)
        val example = App(f, Name("x"))
        assertFail(context, example)
    }

    @Test
    fun `specialization fails - variables constrained to incompatible types`() {
        val context = makeContext("f" to Arrow(B, I), "h" to Arrow(Arrow(a, a), I))
        val example = App(Name("h"), f)
        assertFail(context, example)
    }

    @Test
    fun `instantiation prevents variable clashes`() {
        val context = makeContext("f" to Arrow(a, a))
        val example = App(f, f)
        assertOk(context, example)
    }

    /**
     * f : a -> a -> I applied to two blanks makes both blanks equal to f's variable, and so to each
     * other. The search gives blanks that are equal to each other the same label.
     */
    @Test
    fun `blanks equal through a shared variable are equal to each other`() {
        val num = Blank(labelOnly = true)
        val tru = Blank(labelOnly = true)
        val context = makeContext("f" to Arrow(a, Arrow(a, I)), "Num" to num, "true" to tru)
        val u = OneUnification(context, listOf(App(App(f, Name("Num")), Name("true"))))
        assertTrue(u.ok)
        assertEquals(u.classesOf(num).single(), u.classesOf(tru).single())
    }

    /**
     * Each of these needs one blank to be two different labels, so it cannot type-check however the
     * state's holes are filled. The unifier on main accepted all of them: it recorded what a hole
     * was unified with instead of unifying it, and never compared the records. In the first,
     * `put (put Eib Num true) Num true` makes Eib's second blank `true`'s label L2 (inner put),
     * and then `Num`'s label L1 (outer put), and main recorded both.
     *
     * Found by running the search on main and on TypeGraph and checking the states where they
     * disagreed.
     */
    @ParameterizedTest
    @MethodSource("oneBlankTwoLabels")
    fun `rejects a blank that has to be two different labels`(benchmark: String, state: String, program: String) {
        val example = loadQueryFromFile(benchmark).examples.posNoSubexprs.single { it.toString() == program }
        assertFail(parseSearchState(state), example)
    }

    /**
     * Unification picks which variable names a class arbitrarily, so types are compared up to
     * renaming variables.
     */
    private fun assertSameType(expected: Type, actual: Type?) {
        assertNotNull(actual)
        assertTrue(
            equalUpToVariableRenaming(expected, actual),
            "Expected $expected up to renaming variables, but was $actual"
        )
    }
}
