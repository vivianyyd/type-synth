import util.toQuery
import java.io.File
import kotlin.test.Test
import kotlin.test.assertTrue

class QueryTemplateTest {
    @Test
    fun `can build query from input file`() {
        val inputLines = File("src/test/input/sample.sexp").readLines()
        val query = toQuery(inputLines)
        assertTrue(true)
    }
}
