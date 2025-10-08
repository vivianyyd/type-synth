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
//    private val parent = mutableListOf<Int>()      // parent[i] = representative index
//    private val indexMap = mutableMapOf<Int, Int>()  // maps value -> index
//    private val values = mutableListOf<Int>()        // maps index -> value
//
//    val size: Int
//        get() = parent.size
//
//    private fun addValueIfAbsent(value: Int): Int {
//        return indexMap.getOrPut(value) {
//            val newIndex = parent.size
//            parent.add(newIndex)   // initially points to itself
//            values.add(value)
//            newIndex
//        }
//    }
//
//    fun find(value: Int): Int {
//        val idx = addValueIfAbsent(value)
//        val repIdx = findIndex(idx)
//        return values[repIdx]
//    }
//
//    private fun findIndex(i: Int): Int {
//        if (parent[i] != i) {
//            parent[i] = findIndex(parent[i]) // path compression
//        }
//        return parent[i]
//    }
//
//    fun union(a: Int, b: Int) {
//        val i = addValueIfAbsent(a)
//        val j = addValueIfAbsent(b)
//        val repI = findIndex(i)
//        val repJ = findIndex(j)
//        if (values[repJ] < values[repI]) parent[repI] = repJ
//        else parent[repJ] = repI
//    }

    // parent[i] = parent index of node i; root nodes have parent[i] == i
    private val parent = mutableListOf<Int>()

    // size[i] = size of tree whose root is i (only valid for roots)
    private val treeSize = mutableListOf<Int>()

    // values[i] = integer value associated with index i
    private val values = mutableListOf<Int>()

    // map from integer value -> index in the arrays above
    private val indexOf = mutableMapOf<Int, Int>()

    var componentCount: Int = 0
        private set

    /** Ensure value exists in structure; returns its index. */
    fun add(value: Int): Int {
        indexOf[value]?.let { return it } // already present
        val idx = parent.size
        parent.add(idx)
        treeSize.add(1)
        values.add(value)
        indexOf[value] = idx
        componentCount++
        return idx
    }

    /** Internal: find root index with path compression. */
    private fun findRootIndex(i: Int): Int {
        var x = i
        // find root
        while (parent[x] != x) {
            x = parent[x]!!
        }
        val root = x
        // path-compress
        var cur = i
        while (parent[cur] != cur) {
            val next = parent[cur]
            parent[cur] = root
            cur = next
        }
        return root
    }

    /** Find the canonical (smallest) integer for the set containing [value].
     *  Returns null if [value] is not present. */
    fun find(value: Int): Int? {
        val idx = indexOf[value] ?: return null
        val root = findRootIndex(idx)
        return values[root]
    }

    /** Check whether both values are present and in the same set. */
    fun connected(a: Int, b: Int): Boolean {
        val ia = indexOf[a] ?: return false
        val ib = indexOf[b] ?: return false
        return findRootIndex(ia) == findRootIndex(ib)
    }

    /**
     * Union the sets containing a and b.
     * If a or b are not present, they are added.
     * The resulting set's canonical element will be the smaller of the two set canonicals.
     */
    fun union(a: Int, b: Int) {
        val ia = add(a)
        val ib = add(b)
        var ra = findRootIndex(ia)
        var rb = findRootIndex(ib)
        if (ra == rb) return

        val valA = values[ra]
        val valB = values[rb]

        // Always attach the root with larger canonical value under the root with smaller canonical value.
        if (valA <= valB) {
            parent[rb] = ra
            treeSize[ra] = treeSize[ra] + treeSize[rb]
        } else {
            parent[ra] = rb
            treeSize[rb] = treeSize[rb] + treeSize[ra]
            // after this, rb is root and its values[rb] is the smallest for the merged set
        }
        componentCount--
    }

    /** Return all sets as a map canonicalElement -> list of members (unsorted). */
    fun allSets(): Map<Int, List<Int>> {
        // compress all paths first
        for (i in parent.indices) {
            parent[i] = findRootIndex(i)
        }
        val groups = mutableMapOf<Int, MutableList<Int>>()
        for (i in values.indices) {
            val r = parent[i]
            val canonicalValue = values[r]
            groups.computeIfAbsent(canonicalValue) { mutableListOf() }.add(values[i])
        }
        return groups
    }

    /** Optional convenience: get number of elements currently stored. */
    val size: Int
        get() = parent.size

}
