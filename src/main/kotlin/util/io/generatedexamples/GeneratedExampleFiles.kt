package util.io.generatedexamples

import util.join
import util.write
import java.io.File

private fun generatedTestPath(name: String) = join("src", "test", "input", "sexp", "$name.sexp")

fun writeExamples(contents: String, name: String) = write(generatedTestPath(name), contents)

fun readExamples(name: String): Pair<String, List<String>> {
    val lines = File(generatedTestPath(name)).readText().split('\n')
    return lines.first() to lines.drop(1)
}
