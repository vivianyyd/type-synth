package util

import org.junit.jupiter.api.Test
import util.io.parseSExpr
import kotlin.test.assertEquals

class SExprParserTest {
    @Test
    fun `parses sexprs`() {
        val input = "(def (square x) (* x x))"
        val result = parseSExpr(input)
        assertEquals(result.toString(), input)
    }
}
