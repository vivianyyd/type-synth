package testutil

import query.Example
import query.Examples
import query.Query
import util.join
import java.io.File

fun loadExamples(dir: File): Examples {
    val pos = mutableListOf<Example>()
    val neg = mutableListOf<Example>()

    require(dir.isDirectory) { "Not a directory: $dir" }

    dir.listFiles()?.forEach { file ->
        if (!file.isFile) return@forEach

        when (file.extension) {
            "pos" -> pos
            "neg" -> neg
            else -> null
        }?.let { destination ->
            file.useLines { lines ->
                lines.forEach { line ->
                    if (line.isNotBlank()) destination.add(unsignedExample(line))
                }
            }
        }
    }

    return Examples(pos, neg)
}

/**
 * Parses test where [name] is the extensionless name of a file containing a ground truth type
 * assignment as SExps in the first line followed by SExps of examples labeled with +/-.
 */
fun loadQueryFromFile(name: String): Query {
    val testPath = join("src", "test", "input", "sexp", "$name.sexp")
    val lines = File(testPath).readText().split('\n')
    val (types, exs) = lines.first() to lines.drop(1)

    return Query(
        signedExamplesFromStrings(exs.filter { it.isNotBlank() }),
        oracleFromAssignment(types)
    )
}
