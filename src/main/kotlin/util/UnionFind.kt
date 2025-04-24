package util

class UnionFind(size: Int) {
    private val parent = Array(size) { it }

    // Find the representative (root) of the set that includes element i
    fun find(i: Int): Int = if (parent[i] == i) i else find(parent[i])

    // Merge the set that includes element  i and the set that includes element j
    fun union(i: Int, j: Int) {
        val irep = find(i)
        val jrep = find(j)
        parent[irep] = jrep
    }
}