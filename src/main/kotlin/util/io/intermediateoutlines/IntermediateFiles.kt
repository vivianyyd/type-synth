package util.io.intermediateoutlines

import products.stc.outline
import util.deleteAll
import util.join
import util.write
import java.io.File

private fun intermediateOutlinePath(name: String) =
    join("results", "intermediate", "outline", "outline-$name.sexp")

fun writeIntermediateOutline(contents: String, name: String) =
    write(intermediateOutlinePath(name), contents)

fun readIntermediateOutlines() =
    File(join("results", "intermediate", "outline"))
        .listFiles()!!
        .filter { it.isFile }
        .mapNotNull { file ->
            if (file.isFile)
                file.name.substringAfter("outline-").substringBeforeLast(".sexp").toInt() to
                        outline(file.readText())
            else null
        }
        .sortedBy { it.first }

fun clearOutlines() {
    deleteAll(join("results", "intermediate", "outline"))
}
