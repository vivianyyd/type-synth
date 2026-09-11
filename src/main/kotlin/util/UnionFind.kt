package util

import oneast.ConstraintTy
import oneast.ConstraintTypeConstructor
import oneast.Leaf

/**
 * A union-find over [Leaf]s, suited to Hindley-Milner type unification.
 *
 * Each equivalence class groups the leaves that have been unified together, and may additionally be
 * resolved to a single bound [ConstraintTy] (`null` = still unbound, i.e. a free type variable).
 *
 * Classes are identified by their representative [Leaf] (a canonical member), so all queries take a
 * [Leaf] and return [Leaf]s — there is no separate handle object. The member set and bound type are
 * kept on the representative; [find] resolves any member to it. Weighted union by rank with path
 * compression.
 */
class UnionFind {
    /** Parent pointer per leaf; a representative points to itself. */
    private val parent = hashMapOf<Leaf, Leaf>()

    /** Rank per leaf (only meaningful for representatives). */
    private val rank = hashMapOf<Leaf, Int>()

    /**
     * Members of each class, keyed by representative (non-representatives are removed on union).
     */
    private val memberSet = hashMapOf<Leaf, MutableSet<Leaf>>()

    /** Bound type of each class, keyed by representative; absent = unbound. */
    private val boundType = hashMapOf<Leaf, ConstraintTypeConstructor>()

    /** A snapshot of one equivalence class. */
    data class Class(val members: Set<Leaf>, val bound: ConstraintTypeConstructor?)

    /** Ensure [v] is tracked, returning the representative of its (current) class. */
    fun add(v: Leaf): Leaf {
        if (v in parent) return root(v)
        parent[v] = v
        rank[v] = 0
        memberSet[v] = hashSetOf(v)
        return v
    }

    /** Representative of [v]'s class, with path compression; assumes [v] is present. */
    private fun root(v: Leaf): Leaf {
        var r = v
        while (parent[r] != r) r = parent.getValue(r)
        var cur = v
        while (parent[cur] != cur) {
            val next = parent.getValue(cur)
            parent[cur] = r
            cur = next
        }
        return r
    }

    /** Representative of [v]'s class, or `null` if [v] has never been added. */
    fun find(v: Leaf): Leaf? = if (v in parent) root(v) else null

    /** The type [v]'s class is resolved to, or `null` if [v] is absent or still unbound. */
    fun bound(v: Leaf): ConstraintTypeConstructor? = find(v)?.let { boundType[it] }

    /** All leaves in [v]'s class, or empty if [v] is absent. */
    fun members(v: Leaf): Set<Leaf> = find(v)?.let { memberSet.getValue(it) } ?: emptySet()

    /** Whether [a] and [b] are in the same class (adding either if absent). */
    fun connected(a: Leaf, b: Leaf): Boolean {
        add(a)
        add(b)
        return root(a) == root(b)
    }

    fun union(
        a: Leaf,
        b: ConstraintTy,
        reconcile:
            (ConstraintTypeConstructor, ConstraintTypeConstructor) -> ConstraintTypeConstructor?
    ): Boolean = when (b) {
        is Leaf -> merge(a, b, reconcile)
        is ConstraintTypeConstructor -> bind(a, b, reconcile)
    }

    /**
     * Merge the classes of [a] and [b], adding either if absent. The merged class contains the
     * union of both member sets. Bound types are reconciled: if only one side is bound the merged
     * class keeps it; if both are bound [reconcile] decides the single result. Returns whether
     * union was successful.
     */
    private fun merge(
        a: Leaf,
        b: Leaf,
        reconcile:
            (ConstraintTypeConstructor, ConstraintTypeConstructor) -> ConstraintTypeConstructor?
    ): Boolean {
            add(a)
            add(b)
            val ra = root(a)
            val rb = root(b)
            if (ra == rb) return true

            val ba = boundType[ra]
            val bb = boundType[rb]

            // Link the two classes *before* reconciling. [reconcile] may re-enter this
            // union-find (unifying the two bound constructors can trigger further unions and
            // binds), and that re-entrant work relocates roots and rewrites member sets. If we
            // reconciled first and then linked, the [ra]/[rb] we captured could be stale
            // non-roots by the time we touch [parent]/[memberSet] — corrupting the structure or
            // crashing on the `memberSet.remove(child)!!`. Doing the structural link first means
            // (a) the roots captured just above are still valid (nothing has run in between) and
            // (b) any re-entrant unification sees a single, consistent class.
            //
            // Union by rank: attach the shorter tree (child) under the taller (root).
            val (root, child) =
                when {
                    rank.getValue(ra) < rank.getValue(rb) -> rb to ra
                    rank.getValue(ra) > rank.getValue(rb) -> ra to rb
                    else -> ra.also { rank[it] = rank.getValue(it) + 1 } to rb
                }
            parent[child] = root
            memberSet.getValue(root).addAll(memberSet.remove(child)!!)
            boundType.remove(child)

            val merged: ConstraintTypeConstructor? =
                if (ba != null && bb != null) {
                    reconcile(ba, bb) ?: return false
                } else ba ?: bb

            // [reconcile] above may have relocated this class's root, so resolve it again rather
            // than writing the bound onto the now-possibly-stale [root] (which could have become
            // a non-root, stranding the bound where [find]/[bound] never see it).
            val cur = root(a)
            if (merged != null) boundType[cur] = merged else boundType.remove(cur)
            return true
        }

        /**
         * Bind [v]'s class to [type]. Binding an unbound class sets it; rebinding to an equal type is a
         * no-op. Rebinding to a *different* type calls [reconcile] with `(existing, type)`: a non-null
         * result becomes the new bound type and binding succeeds; a null result is a conflict, leaving
         * the existing bound type untouched and returning `false`.
         */
        private fun bind(
            v: Leaf,
            type: ConstraintTypeConstructor,
            reconcile:
                (ConstraintTypeConstructor, ConstraintTypeConstructor) -> ConstraintTypeConstructor?
        ): Boolean {
            val r = add(v)
            val existing = boundType[r]
            if (existing == null || existing == type) {
                boundType[r] = type
                return true
            }
            val merged = reconcile(existing, type) ?: return false
            // [reconcile] may have re-entered this union-find and relocated [v]'s class, so
            // resolve the root again rather than writing the bound onto the stale [r] (which
            // could now be a non-root, stranding the bound where [find]/[bound] never see it).
            boundType[root(v)] = merged
            return true
        }

    /** A snapshot of all current equivalence classes. */
    val classes: Collection<Class>
        get() = memberSet.map { (rep, ms) -> Class(ms.toSet(), boundType[rep]) }

    /**
     * A human-readable rendering of every equivalence class, one per line, each as the set of its
     * members optionally followed by `= <bound type>` when the class is bound. Members within a
     * class and the classes themselves are sorted by their [toString] so the output is stable
     * regardless of insertion or union order.
     */
    override fun toString(): String {
        if (memberSet.isEmpty()) return "UnionFind(empty)"
        val lines =
            memberSet
                .map { (rep, ms) ->
                    val members = ms.map { it.toString() }.sorted().joinToString(", ", "{", "}")
                    val bound = boundType[rep]
                    if (bound != null) "$members = $bound" else members
                }
                .sorted()
        return lines.joinToString("\n", "UnionFind(\n", "\n)") { "  $it" }
    }
}

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
