package fixtures

import query.Example
import query.Examples
import util.io.toExample
import java.io.File

fun loadQuery(dir: File): Examples {
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
                lines.forEach { line -> if (line.isNotBlank()) destination.add(line.toExample()) }
            }
        }
    }

    return Examples(pos, neg)
}
