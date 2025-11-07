/** AI-generated code I was toying with */

interface P {
    fun expansions(bound: Int): List<P>
    fun containsHole(): Boolean
}

object X : P {
    override fun toString() = "X"
    override fun expansions(bound: Int) = listOf(X)
    override fun containsHole() = false
}

data class K(val l: P, val r: P) : P {
    override fun toString() = "F($l,$r)"
    override fun containsHole() = l.containsHole() || r.containsHole()
    override fun expansions(bound: Int) =
        l.expansions(bound - 1).flatMap { le -> r.expansions(bound - 1).map { re -> K(le, re) } }
}

class Hole private constructor(val id: Int) : P {
    companion object {
        var fresh = 0
        fun new() = Hole(fresh++)
    }

    override fun containsHole() = true

    override fun toString() = "?$id"

    override fun expansions(bound: Int) = if (bound < 1) listOf(X) else listOf(X, K(new(), new()))
}

fun commitLeftmost(c: List<P>, recursionBound: Int): List<List<P>> {
    val (changeInd, leftmostNode) = c.withIndex().firstOrNull { (i, it) -> it.containsHole() } ?: return listOf(c)

    val optionsForLeftmost = leftmostNode.expansions(recursionBound)
    return optionsForLeftmost.flatMap { newLeftMost ->
        val newCandidate = c.mapIndexed { i, p -> if (changeInd == i) newLeftMost else p }
        commitLeftmost(newCandidate, recursionBound)
    }
}


fun main() {

    println(commitLeftmost(List(3) { Hole.new() }, 3).take(200).joinToString(separator = "\n"))
}
