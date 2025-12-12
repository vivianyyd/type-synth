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

class UnionFind<T>(private val isTypeConstructor: (T) -> Boolean) {
    class Node<T>(var value: T) {
        var parent: Node<T> = this
        var rank: Int = 0
    }

    private val nodes = mutableMapOf<T, Node<T>>()

    fun copy(): UnionFind<T> {
        val new = UnionFind(isTypeConstructor)
        nodes.forEach { (t, _) -> new.union(t, find(t)) }
        return new
    }

    fun rootsFor(selector: (T) -> Boolean) =
        nodes.mapNotNull { if (selector(it.key)) find(it.value).value else null }

    fun filterNodes(selector: (T) -> Boolean) = nodes.keys.filter { selector(it) }

    fun replaceRoots(transform: Map<T, T>) {
        val toTransform =
            nodes.toList().filter {
                it.second.parent == it.second && it.first in transform
            } // two conditions should be equiv
        //        val newNodesToMapTo =
        toTransform.forEach { (k, v) ->
            v.value = transform[k]!!
            nodes.remove(k)
            nodes[v.value] = v
        }
        //        toTransform.forEach{nodes.remove(it.key)}
        //        newNodesToMapTo
    }

    fun allRootValues() = nodes.values.filter { it.parent == it }.map { it.value }.toSet()

    fun makeSet(x: T) {
        if (x !in nodes) {
            nodes[x] = Node(x)
        }
    }

    private fun find(node: Node<T>): Node<T> {
        if (node.parent != node) {
            node.parent = find(node.parent) // Path compression
        }
        return node.parent
    }

    private fun nodeOf(value: T): Node<T> = nodes.getOrPut(value) { Node(value) }

    fun find(value: T): T {
        return find(nodeOf(value)).value
    }

    fun union(x: T, y: T) {
        var rootX = find(nodeOf(x))
        var rootY = find(nodeOf(y))

        if (rootX == rootY) return

        val xMustBeRoot = isTypeConstructor(rootX.value)
        val yMustBeRoot = isTypeConstructor(rootY.value)

        when {
            xMustBeRoot && yMustBeRoot -> {
                throw IllegalStateException(
                    "Invariant violated: more than one constructor in the same class"
                )
            }
            xMustBeRoot -> rootY.parent = rootX // x remains root
            yMustBeRoot -> rootX.parent = rootY // y remains root
            else -> {
                // Neither has check true — use union by rank
                when {
                    rootX.rank < rootY.rank -> rootX.parent = rootY
                    rootX.rank > rootY.rank -> rootY.parent = rootX
                    else -> {
                        rootY.parent = rootX
                        rootX.rank = rootX.rank + 1
                    }
                }
            }
        }
    }

    fun remove(x: T) {
        if (x !in nodes) return
        val xNode = nodes[x]!!
        // Reassign any children that pointed to this element
        for ((_, node) in nodes) {
            if (node.parent == xNode) {
                node.parent = xNode.parent
            }
        }
        nodes.remove(x)
    }

    fun connected(x: T, y: T): Boolean = find(x) == find(y)

    fun representative(x: T): T = find(x)
}

fun main() {
    val uf = UnionFind<Int> { it == 1 } // only 1 is "special"

    // Setup initial sets
    (1..5).forEach { uf.makeSet(it) }

    uf.union(1, 2)
    uf.union(3, 4)
    uf.union(4, 5)

    // Test equivalence before removal
    println(uf.connected(1, 2)) // true
    println(uf.connected(3, 5)) // true
    println(uf.connected(2, 3)) // false

    // Remove a non-root element
    uf.remove(2)
    try {
        println(uf.connected(1, 2))
    } catch (e: Exception) {
        println("ok")
    } // false (2 removed)
    println(uf.connected(1, 1)) // true
    println(uf.connected(3, 5)) // true, should remain intact

    // Remove a root element without "special" check
    uf.remove(4)
    println(uf.connected(3, 5)) // true, equivalence class intact
    try {
        println(uf.connected(4, 5)) // false (4 removed)
    } catch (e: Exception) {
        println("ok")
    }

    // Remove the "special" root
    uf.remove(1)
    try {
        println(uf.connected(1, 1)) // false (1 removed)
    } catch (e: Exception) {
        println("ok")
    }
    try {
        println(uf.connected(1, 3)) // false
    } catch (e: Exception) {
        println("ok")
    }
    println(uf.connected(3, 5)) // true, other set intact

    // Check union after removals
    uf.union(5, 3)
    println(uf.connected(5, 3)) // true
}

/*
class UnionFind<T>(
    private val isTypeConstructor: (T) -> Boolean
) {

    private val parent = mutableMapOf<T, T>()
    private val rank = mutableMapOf<T, Int>()

    fun allRoots() = parent.keys.filter { key -> parent[key] == key }.toSet()
    // should not be a set, since some roots may be equal to one another by being independently produced without getting
    // explicitly unioned.

    fun makeSet(x: T) {
        if (x !in parent) {
            parent[x] = x
            rank[x] = 0
        }
    }

    fun find(x: T): T {
        val px = parent[x] ?: throw IllegalArgumentException("Element $x not found")
        if (px != x) {
            parent[x] = find(px) // path compression
        }
        return parent[x]!!
    }

    fun union(x: T, y: T) {
        var rootX = find(x)
        var rootY = find(y)

        if (rootX == rootY) return

        val xMustBeRoot = isTypeConstructor(rootX)
        val yMustBeRoot = isTypeConstructor(rootY)

        when {
            xMustBeRoot && yMustBeRoot -> {
                throw IllegalStateException("Invariant violated: more than one constructor in the same class")
            }
            xMustBeRoot -> parent[rootY] = rootX // x remains root
            yMustBeRoot -> parent[rootX] = rootY // y remains root
            else -> {
                // Neither has check true — use union by rank
                val rankX = rank[rootX]!!
                val rankY = rank[rootY]!!
                when {
                    rankX < rankY -> parent[rootX] = rootY
                    rankX > rankY -> parent[rootY] = rootX
                    else -> {
                        parent[rootY] = rootX
                        rank[rootX] = rankX + 1
                    }
                }
            }
        }
    }

    fun remove(x: T) {
        val root = parent[x] ?: return // element not present, nothing to do

        // Remove the element from the parent map
        parent.remove(x)
        rank.remove(x)

        // Reassign any children that pointed to this element
        for ((key, value) in parent) {
            if (value == x) {
                parent[key] = root // make it a new root of its own
            }
        }
    }

    fun connected(x: T, y: T): Boolean = find(x) == find(y)

    fun representative(x: T): T = find(x)
}
 */
