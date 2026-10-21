package util

import org.junit.jupiter.api.Test
import testutil.ocaml.loadFromExsFiles
import testutil.ocaml.ocamlModuleGroups
import testutil.ocamlName
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class OCamlNamesTest {
    @Test
    fun `operators are parenthesized without spaces`() {
        assertEquals("(*)", ocamlName("*"))
        assertEquals("(*.)", ocamlName("*."))
        assertEquals("(**)", ocamlName("**"))
        assertEquals("(+)", ocamlName("+"))
        assertEquals("(~-.)", ocamlName("~-."))
    }

    @Test
    fun `word operators are operators`() {
        assertEquals("(mod)", ocamlName("mod"))
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
