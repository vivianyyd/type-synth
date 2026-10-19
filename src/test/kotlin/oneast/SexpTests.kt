package oneast

import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource
import testutil.loadQueryFromFile
import testutil.sexpDir

class SexpTests {
    companion object {
        @JvmStatic
        fun testNames() =
            sexpDir.listFiles()!!.filter { it.extension == "sexp" }.map { it.nameWithoutExtension }.sorted()
    }

    @ParameterizedTest
    @MethodSource("testNames")
    fun `validate tests`(name: String) {
        val query = loadQueryFromFile(name)
        query.examples.posNoSubexprs.forEach {
            assert(query.oracle.valid(it)) { "Bad positive example: $it" }
        }
        query.examples.neg.forEach {
            assert(!query.oracle.valid(it)) { "Bad negative example: $it" }
        }
    }
}
