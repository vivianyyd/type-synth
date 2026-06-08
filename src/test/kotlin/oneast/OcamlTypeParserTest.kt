package oneast

import testutil.ocaml.OcamlTypeParser
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class OcamlTypeParserTest {
    private fun parse(sig: String): Type =
        OcamlTypeParser().parseSignatures("val x : $sig").getValue("x")

    /** A [NamedLabel] regardless of its (encounter-order-dependent) label id. */
    private fun Type.asLabel(): NamedLabel = this as NamedLabel

    @Test
    fun `postfix application is left-associative and applies to the preceding atom`() {
        // 'a list -> list applied to 'a, not 'a applied to list.
        val t = parse("'a list").asLabel()
        assertEquals(listOf(Variable(0)), t.params)

        // 'a list list == list (list 'a)
        val ll = parse("'a list list").asLabel()
        val inner = ll.params.single().asLabel()
        assertEquals(listOf(Variable(0)), inner.params)
        // Both applications use the same `list` constructor label.
        assertEquals(ll.label, inner.label)
    }

    @Test
    fun `arrows are right associative`() {
        val t = parse("'a -> 'b -> 'c")
        // 'a -> ('b -> 'c)
        val outer = t as Arrow
        assertEquals(Variable(0), outer.l)
        val inner = outer.r as Arrow
        assertEquals(Variable(1), inner.l)
        assertEquals(Variable(2), inner.r)
    }

    @Test
    fun `parentheses regroup arrows for higher-order functions`() {
        // ('a -> 'b) -> 'a list -> 'b list  (map)
        val t = parse("('a -> 'b) -> 'a list -> 'b list") as Arrow
        assertTrue(t.l is Arrow, "first argument should itself be a function type")
        val rest = t.r as Arrow
        assertEquals(listOf(Variable(0)), rest.l.asLabel().params)
        assertEquals(listOf(Variable(1)), rest.r.asLabel().params)
    }

    @Test
    fun `tuple types become a label with one parameter per component`() {
        // Parse within one parser so constructor labels are comparable.
        val parser = OcamlTypeParser()
        val types = parser.parseSignatures(
            """
            val p : 'a * 'b
            val t : 'a * 'b * 'c
            """.trimIndent()
        )
        val pair = types.getValue("p").asLabel()
        assertEquals(listOf(Variable(0), Variable(1)), pair.params)

        val triple = types.getValue("t").asLabel()
        assertEquals(listOf(Variable(0), Variable(1), Variable(2)), triple.params)

        // A pair and a triple are *different* constructors.
        assertTrue(pair.label != triple.label)
    }

    @Test
    fun `application binds tighter than tuple which binds tighter than arrow`() {
        // 'acc * 'b list == ('acc) * ('b list), nested under no arrow here.
        val t = parse("'acc * 'b list").asLabel()
        assertEquals(2, t.params.size)
        assertEquals(Variable(0), t.params[0]) // 'acc
        assertEquals(listOf(Variable(1)), t.params[1].asLabel().params) // 'b list

        // ('a * 'b) list == list of a pair.
        val listOfPair = parse("('a * 'b) list").asLabel()
        assertEquals(2, listOfPair.params.single().asLabel().params.size)
    }

    @Test
    fun `multi-parameter module-qualified constructors`() {
        // Parse within one parser so constructor labels are comparable.
        val parser = OcamlTypeParser()
        val types = parser.parseSignatures(
            """
            val e : ('b, 'c) Either.t
            val s : 'a Seq.t
            """.trimIndent()
        )
        // ('b, 'c) Either.t -> Either.t applied to two arguments.
        val t = types.getValue("e").asLabel()
        assertEquals(listOf(Variable(0), Variable(1)), t.params)

        // 'a Seq.t -> single-parameter module-qualified postfix application.
        val seq = types.getValue("s").asLabel()
        assertEquals(listOf(Variable(0)), seq.params)
        // Distinct constructors despite both ending in `.t`.
        assertTrue(t.label != seq.label)
    }

    @Test
    fun `constructor labels are shared across signatures within one parser`() {
        val parser = OcamlTypeParser()
        val types = parser.parseSignatures(
            """
            val hd : 'a list -> 'a
            val length : 'a list -> int
            """.trimIndent()
        )
        val hdList = ((types.getValue("hd")) as Arrow).l as NamedLabel
        val lengthList = ((types.getValue("length")) as Arrow).l as NamedLabel
        assertEquals(hdList.label, lengthList.label)
    }
}
