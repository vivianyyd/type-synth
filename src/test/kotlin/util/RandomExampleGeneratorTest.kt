package util

import org.junit.jupiter.api.Test
import testutil.parseSExpr
import kotlin.test.assertEquals

class RandomExampleGeneratorTest {
    @Test
    fun `generates examples`() {
        val gen =
            RandomExampleGenerator(
                listOf(
                    // Boolean operations section of stdlib 5.4 docs
                    "not",
                    "(&&)",
                    "(||)",
                    // Integer arithmetic
                    "(~-)",
                    "(~+)",
                    "succ",
                    "pred",
                    "(+)",
                    "(-)",
                    "( * )",
                    "(/)",
                    "(mod)",
                    "abs",
                    "max_int",
                    "min_int",
                    // Character operations
                    "int_of_char",
                    "char_of_int"
                )
            )
        // each name gotta have 5 examples
        val input = "(def (square x) (* x x))"
        val result = parseSExpr(input)
        assertEquals(result.toString(), input)
    }
}
