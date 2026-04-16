package util

import org.junit.jupiter.api.Disabled
import org.junit.jupiter.api.Test

class RandomExampleGeneratorTest {
    @Test
    @Disabled
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
    }
}
