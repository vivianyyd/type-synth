/** AI-generated code I was toying with */
import util.partitions
import java.io.File

fun f(line: String): String {
    return line.split(": ").map {
        val noHoles = it.replace(Regex("_[0-9]+_"), "_")
            .replace(Regex("☐[0-9]+"), "_")
        val regex = Regex("V\\d+")

        val vars = mutableMapOf<String, String>()
        var counter = 0
        fun g(x: String): String =
            vars.getOrPut(x) { "V${counter++}" }

        val result = regex.replace(noHoles) { match ->
            g(match.value)
        }
        result

    }.joinToString(separator = ": ")
}

fun processFile(inputPath: String, outputPath: String) {
    File(inputPath).useLines { lines ->
        File(outputPath).printWriter().use { writer ->
            lines.forEach { line ->
//                writer.println("Was: $line")
//                writer.println("Now: ${f(line)}")
                if ("Now:" in line) {
                    writer.println(
                        line.replace("b: L0[], ", "")
                            .replace("dbb: L1[_, _], dbi: L1[_, _], dib: L1[_, _], dii: L1[_, _], i: L8[], ", "")
                    )
                }
            }
        }
    }
}

fun main() {
//    processFile("canonicalized.txt", "only-canonicalized.txt")

    var count = 0
    partitions(listOf(1, 2, 3, 4, 5, 6)).forEach {
        println(it)
        count++
    }
    println(count)

//    println(commitLeftmost(List(3) { Hole.new() }, 3).take(200).joinToString(separator = "\n"))
}


//interface P {
//    fun expansions(bound: Int): List<P>
//    fun containsHole(): Boolean
//}

//object X : P {
//    override fun toString() = "X"
//    override fun expansions(bound: Int) = listOf(X)
//    override fun containsHole() = false
//}
//
//data class K(val l: P, val r: P) : P {
//    override fun toString() = "F($l,$r)"
//    override fun containsHole() = l.containsHole() || r.containsHole()
//    override fun expansions(bound: Int) =
//        l.expansions(bound - 1).flatMap { le -> r.expansions(bound - 1).map { re -> K(le, re) } }
//}
//
//class Hole private constructor(val id: Int) : P {
//    companion object {
//        var fresh = 0
//        fun new() = Hole(fresh++)
//    }
//
//    override fun containsHole() = true
//
//    override fun toString() = "?$id"
//
//    override fun expansions(bound: Int) = if (bound < 1) listOf(X) else listOf(X, K(new(), new()))
//}
//
//fun commitLeftmost(c: List<P>, recursionBound: Int): List<List<P>> {
//    val (changeInd, leftmostNode) = c.withIndex().firstOrNull { (i, it) -> it.containsHole() } ?: return listOf(c)
//
//    val optionsForLeftmost = leftmostNode.expansions(recursionBound)
//    return optionsForLeftmost.flatMap { newLeftMost ->
//        val newCandidate = c.mapIndexed { i, p -> if (changeInd == i) newLeftMost else p }
//        commitLeftmost(newCandidate, recursionBound)
//    }
//}

