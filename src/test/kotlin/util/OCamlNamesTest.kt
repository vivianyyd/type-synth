package util

import org.junit.jupiter.api.Test
import testutil.ocaml.loadFromExsFiles
import testutil.ocaml.ocamlModuleGroups
import testutil.ocamlName
import testutil.unsignedExample
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class OCamlNamesTest {
    @Test
    fun `operators starting or ending with a star get spaces`() {
        assertEquals("( * )", ocamlName("*"))
        assertEquals("( *. )", ocamlName("*."))
        assertEquals("( ** )", ocamlName("**"))
        assertEquals("(+)", ocamlName("+"))
        assertEquals("(~-.)", ocamlName("~-."))
    }

    @Test
    fun `word operators are operators`() {
        assertEquals("( mod )", ocamlName("mod"))
        assertEquals("(land)", ocamlName("land"))
    }

    @Test
    fun `names without letters are parenthesized`() {
        assertEquals("({})", ocamlName("{}"))
    }

    @Test
    fun `other names are left alone`() {
        listOf("succ", "Num", "List.map", "x'", "max_int").forEach { assertEquals(it, ocamlName(it)) }
    }

    @Test
    fun `examples name operators the way type signatures do`() {
        assertEquals(setOf("( *. )", "Flt"), unsignedExample("(( *. ) Flt Flt)").names)
        assertEquals(setOf("( ** )", "Flt"), unsignedExample("(** Flt Flt)").names)
    }

    /**
     * Examples whose names have no type are dropped from the OCaml benchmarks without a word. Lambdas'
     * variables and arrows never have types, but an operator spelled differently in the examples
     * than in the signatures would go unnoticed.
     */
    @Test
    fun `every operator in the OCaml benchmarks' examples has a type`() {
        val (examples, types) = loadFromExsFiles(ocamlModuleGroups.flatten())
        val untyped = examples.flatMap { it.names }.toSet() - types.keys
        val operators = untyped.filter { it.startsWith("(") && it != "(->)" }
        assertTrue(operators.isEmpty(), "No type for $operators")
    }
}
