import util.io.parseExamples
import java.io.File
import kotlin.test.Test
import kotlin.test.assertTrue

class ExamplesTemplateTest {
    @Test
    fun `can build query from input file`() {
        val inputLines = File("src/test/input/sample.sexp").readLines()
        val query = parseExamples(inputLines.filter { it.isNotBlank() })
        assertTrue(true)
    }
}
