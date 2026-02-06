package scratch

import query.App
import query.Query
import query.parseTest
import query.vizUndir

/** AI-generated code I was toying with */
fun main() {
    val querySpec = parseTest("dictchain")
    val query = querySpec.query
    vizUndir(query)

    // Example: 12 nodes (0..11)
    val n = query.names.size
    val matrix = Array(n) { IntArray(n) { 0 } }
    val indices = query.names.withIndex().associate { (i, n) -> n to i }
    query.posNoSubexprs.filterIsInstance<App>().forEach {
        it.names.forEach { n1 ->
            it.names.forEach { n2 ->
                val i1 = indices[n1]!!
                val i2 = indices[n2]!!
                matrix[i1][i2] += 1
                matrix[i2][i1] += 1
            }
        }
    }

    val (A, B) = balancedMinCut(matrix, cushion = 3, iterations = 20)
    println("Set A: ${A.map { query.names[it] }}}")
    println("Set B: ${B.map { query.names[it] }}}")

    // Compute cut weight
    val cutWeight = A.sumOf { i -> B.sumOf { j -> matrix[i][j] } }
    println("Cut weight: $cutWeight")

    //    val G = Graph(n, matrix)
    //    val subset = findDenseWeaklyConnectedSubset(G)
    //
    //    println("Chosen subset: ${subset.map { query.names[it] }}")
    //    println("Internal density = ${internalDensity(G, subset)}")
    //    println("External density = ${externalDensity(G, subset)}")
}

fun balancedMinCut(
    matrix: Array<IntArray>,
    cushion: Int = 0,
    iterations: Int = 10
): Pair<Set<Int>, Set<Int>> {
    val n = matrix.size
    if (n == 0) return emptySet<Int>() to emptySet<Int>()

    // Initial random split roughly in half
    val nodes = (0 until n).toList()
    val shuffled = nodes.shuffled()
    val portion = n / 3 // TODO tunable. for half was n/2
    var A = shuffled.take(portion).toMutableSet()
    var B = shuffled.drop(portion).toMutableSet()

    fun cutWeight(): Int {
        var sum = 0
        for (i in A) for (j in B) sum += matrix[i][j]
        return sum
    }

    repeat(iterations) {
        // Compute gain for all movable nodes
        val gains = mutableListOf<Triple<Int, Int, Int>>() // node, fromSetSize, gain
        for (i in nodes) {
            val fromSet = if (A.contains(i)) A else B
            val toSet = if (fromSet === A) B else A
            if (fromSet.size - 1 < portion - cushion || fromSet.size - 1 > portion + cushion)
                continue

            val internal = fromSet.sumOf { j -> matrix[i][j] }
            val external = toSet.sumOf { j -> matrix[i][j] }
            val gain = external - internal
            gains.add(Triple(i, fromSet.size, gain))
        }

        if (gains.isEmpty()) return@repeat

        // Move the node with max gain
        val (nodeToMove, _, _) = gains.maxByOrNull { it.third }!!
        if (A.contains(nodeToMove)) {
            A.remove(nodeToMove)
            B.add(nodeToMove)
        } else {
            B.remove(nodeToMove)
            A.add(nodeToMove)
        }
    }

    return A to B
}

data class Graph(val n: Int, val matrix: Array<IntArray>) {
    // n = number of nodes
    // matrix[i][j] = number of edges from i -> j (undirected)

    fun edgesInside(subset: Set<Int>): Int {
        var total = 0
        val nodes = subset.toList()
        for (i in nodes.indices) {
            for (j in i + 1 until nodes.size) {
                total += matrix[nodes[i]][nodes[j]]
            }
        }
        return total
    }

    fun edgesBetween(subset: Set<Int>): Int {
        val others = (0 until n).toSet() - subset
        var total = 0
        for (u in subset) {
            for (v in others) {
                total += matrix[u][v]
            }
        }
        return total
    }
}

fun internalDensity(G: Graph, S: Set<Int>): Double {
    if (S.size <= 1) return 0.0
    val possible = S.size * (S.size - 1) / 2.0
    return G.edgesInside(S) / possible
}

fun externalDensity(G: Graph, S: Set<Int>): Double {
    val others = G.n - S.size
    if (S.isEmpty() || others == 0) return 0.0
    val possible = S.size * others.toDouble()
    return G.edgesBetween(S) / possible
}

fun findDenseWeaklyConnectedSubset(G: Graph): Set<Int> {
    var bestSet = emptySet<Int>()
    var bestScore = Double.NEGATIVE_INFINITY

    for (start in 0 until G.n) {
        var current = mutableSetOf(start)
        var improved = true
        while (improved) {
            improved = false
            val candidates = (0 until G.n).toSet() - current
            val next =
                candidates.maxByOrNull { v ->
                    val newSet = current + v
                    internalDensity(G, newSet) - externalDensity(G, newSet)
                }
            if (next != null) {
                val newSet = current + next
                val score = internalDensity(G, newSet) - externalDensity(G, newSet)
                if (score > internalDensity(G, current) - externalDensity(G, current)) {
                    current = newSet.toMutableSet()
                    improved = true
                }
            }
        }
        val score =
            (internalDensity(G, current) - 0.3 * externalDensity(G, current)) *
                    Math.log(1.0 + current.size)
        val epsilon = 10 // TODO tunable
        if (score >= bestScore - epsilon) {
            bestScore = score
            bestSet = current
        }
    }
    return bestSet
}
