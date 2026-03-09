package util

class OldUnionFind(initialSize: Int = 0) {
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

class IntUnionFind {
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
        indexOf[value]?.let {
            return it
        } // already present
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
            x = parent[x]
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

    /**
     * Find the canonical (smallest) integer for the set containing [value]. Returns null if [value]
     * is not present.
     */
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
     * Union the sets containing a and b. If a or b are not present, they are added. The resulting
     * set's canonical element will be the smaller of the two set canonicals.
     */
    fun union(a: Int, b: Int) {
        val ia = add(a)
        val ib = add(b)
        var ra = findRootIndex(ia)
        var rb = findRootIndex(ib)
        if (ra == rb) return

        val valA = values[ra]
        val valB = values[rb]

        // Always attach the root with larger canonical value under the root with smaller canonical
        // value.
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

/**
 * Generic union-find (disjoint-set) data structure for elements of type [T].
 *
 * We use a map-based representation instead of index arrays: `parent` maps every element directly
 * to its parent element (roots map to themselves), and `treeSize` maps each root to its subtree
 * size. This eliminates the need for a separate `values` list and `indexOf` reverse-map that
 * [IntUnionFind] requires, because elements of an arbitrary type [T] are not naturally associated
 * with consecutive integer indices. The map approach keeps the code simpler and equally efficient
 * (O(α(n)) amortized per operation with path compression and union-by-size).
 *
 * [T] must be [Comparable] so that we can preserve the same "canonical element = smallest in the
 * set" invariant that [IntUnionFind] provides.
 */
class UnionFind<T : Comparable<T>> {
    // parent[x] = parent of x; root elements satisfy parent[x] == x
    private val parent = mutableMapOf<T, T>()

    // treeSize[x] = number of nodes in the tree rooted at x (only meaningful for roots)
    private val treeSize = mutableMapOf<T, Int>()

    var componentCount: Int = 0
        private set

    /** Ensure [value] exists in the structure. Returns true if it was newly added. */
    fun add(value: T): Boolean {
        if (value in parent) return false
        parent[value] = value
        treeSize[value] = 1
        componentCount++
        return true
    }

    /** Internal: find the root of [value]'s set with iterative path compression. */
    private fun findRoot(value: T): T {
        var x = value
        // Walk up to the root.
        while (parent[x] != x) {
            x = parent[x]!!
        }
        val root = x
        // Path-compress: point every visited node directly at the root.
        var cur = value
        while (parent[cur] != cur) {
            val next = parent[cur]!!
            parent[cur] = root
            cur = next
        }
        return root
    }

    /**
     * Find the canonical (smallest) element of the set containing [value]. Returns null if
     * [value] is not present.
     */
    fun find(value: T): T? {
        if (value !in parent) return null
        return findRoot(value)
    }

    /** Returns true if both values are present and belong to the same set. */
    fun connected(a: T, b: T): Boolean {
        if (a !in parent || b !in parent) return false
        return findRoot(a) == findRoot(b)
    }

    /**
     * Union the sets containing [a] and [b], adding either element if not yet present. The
     * canonical element of the merged set is the lesser of the two current canonicals, preserving
     * the smallest-wins invariant.
     */
    fun union(a: T, b: T) {
        add(a)
        add(b)
        val ra = findRoot(a)
        val rb = findRoot(b)
        if (ra == rb) return

        // Attach the root with the larger canonical value under the one with the smaller canonical
        // value so that the smaller canonical always remains the root. This mirrors IntUnionFind's
        // union strategy: canonical-value comparison is the tie-breaker, not tree size. treeSize is
        // still maintained so the field is available for any future size-based heuristics.
        if (ra <= rb) {
            parent[rb] = ra
            treeSize[ra] = treeSize[ra]!! + treeSize[rb]!!
        } else {
            parent[ra] = rb
            treeSize[rb] = treeSize[rb]!! + treeSize[ra]!!
        }
        componentCount--
    }

    /** Return all sets as a map from canonical element to list of members (unsorted). */
    fun allSets(): Map<T, List<T>> {
        // Compress all paths first so parent[x] is the root for every x.
        // findRoot only writes existing entries (never adds/removes keys), so iterating
        // parent.keys directly while updating values is safe.
        for (x in parent.keys) {
            parent[x] = findRoot(x)
        }
        val groups = mutableMapOf<T, MutableList<T>>()
        for (x in parent.keys) {
            val root = parent[x]!!
            groups.getOrPut(root) { mutableListOf() }.add(x)
        }
        return groups
    }

    /** Number of elements currently stored. */
    val size: Int
        get() = parent.size
}
