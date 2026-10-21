package testutil

import org.junit.jupiter.api.Test
import query.App
import query.Name
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertTrue

class SExprParserTest {
    @Test
    fun `parses sexprs`() {
        val input = "(def (square x) (* x x))"
        val result = parseSExpr(input)
        assertEquals(result.toString(), input)
    }

    @Test
    fun `an example that passes a labelled or optional argument is an error`() {
        for (s in listOf(
            "(Hashtbl.create ~random:true Num)", "(Hashtbl.create ?random:true Num)",
            "(List.iter ~f succ Nil)", "(f ?x)", "(f ~_x:Num)", "~f:succ",
        )) {
            val e = assertFailsWith<IllegalArgumentException>(s) { unsignedExample(s) }
            assertTrue("labelled" in e.message!!, e.message)
        }
    }

    @Test
    fun `prefix operators that start with a tilde are not labels`() {
        assertEquals(App(Name("(~-)"), Name("Num")), unsignedExample("((~-) Num)"))
        assertEquals(App(Name("(~-.)"), Name("Flt")), unsignedExample("(~-. Flt)"))
        assertEquals(Name("(~+)"), unsignedExample("~+"))
    }

    @Test
    fun `text after an expression is an error, so an example cannot have a trailing comment`() {
        assertFailsWith<IllegalArgumentException> { parseSExpr("(f x) // note") }
    }
}
