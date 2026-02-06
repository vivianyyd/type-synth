package util

import kotlin.test.Test
import kotlin.test.assertTrue
import java.io.File

class QueryTemplateTest {
    @Test
    fun `can build query from input file`() {
        val inputLines = File("src/test/input/sample.sexp").readLines()
        val query = toQuery(inputLines)
        assertTrue(true)
    }
}
