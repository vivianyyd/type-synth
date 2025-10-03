package util

class UnionFind(initialSize: Int = 0) {
    private val parent = mutableListOf<Int>()

    init {
        repeat(initialSize) { parent.add(it) }
    }

    val size = parent.size

    fun add(): Int {
        val newIndex = parent.size
        parent.add(newIndex)
        return newIndex
    }

    fun find(i: Int): Int {
        if (parent[i] != i) {
            parent[i] = find(parent[i]) // Path compression
        }
        return parent[i]
    }

    fun union(i: Int, j: Int) {
        val irep = find(i)
        val jrep = find(j)
        parent[irep] = jrep
    }
}

class TUnionFind {
    private val parent = mutableListOf<Int>()      // parent[i] = representative index
    private val indexMap = mutableMapOf<Int, Int>()  // maps value -> index
    private val values = mutableListOf<Int>()        // maps index -> value

    val size: Int
        get() = parent.size

    private fun addValueIfAbsent(value: Int): Int {
        return indexMap.getOrPut(value) {
            val newIndex = parent.size
            parent.add(newIndex)   // initially points to itself
            values.add(value)
            newIndex
        }
    }

    fun find(value: Int): Int {
        val idx = addValueIfAbsent(value)
        val repIdx = findIndex(idx)
        return values[repIdx]
    }

    private fun findIndex(i: Int): Int {
        if (parent[i] != i) {
            parent[i] = findIndex(parent[i]) // path compression
        }
        return parent[i]
    }

    fun union(a: Int, b: Int) {
        val i = addValueIfAbsent(a)
        val j = addValueIfAbsent(b)
        val repI = findIndex(i)
        val repJ = findIndex(j)
        if (values[repJ] < values[repI]) parent[repI] = repJ
        else parent[repJ] = repI
    }
}
