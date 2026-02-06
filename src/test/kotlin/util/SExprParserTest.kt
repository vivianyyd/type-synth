package util

import org.junit.jupiter.api.Test
import kotlin.test.assertEquals

class SExprParserTest {
    @Test
    fun `parses sexprs`() {
        val input = "(def (square x) (* x x))"
        val parser = SExprParser(input)
        val result = parser.parse()
        assertEquals(result.toString(), input)
    }
}
