package oneast

import util.IntVec
import util.LongVec

/**
 * A store of type terms under syntactic unification, with an undo journal.
 *
 * Terms are nodes, identified by [Int]. A node's own shape never changes; what changes is which
 * nodes are known to denote the same type, which is tracked by union-find. Each *class* (union-find
 * root) remembers the constructor, rigid variable and hole nodes it contains, so a merge only has
 * to look at the two roots.
 *
 * Every write is journalled, so [rewindTo] restores an earlier state exactly. That is what makes
 * checking a refinement cheap: a child search state differs from its parent only in that one hole
 * has grown into a type, so it can be checked by merging that growth into the parent's graph
 * (O(occurrences of the hole)) rather than re-deriving the whole thing (O(size of all examples)).
 *
 * There are four kinds of node:
 * - **constructor** — an arrow or a label applied to argument nodes.
 * - **rigid** — the instance of a component type's [Variable] at one instantiation.
 * - **hole** — the instance of a [THole] at one instantiation. Unifies like an ordinary variable;
 *   the types it ends up equal to are what [Unification.holeEquals] reports back to the search.
 * - **fresh** — an anonymous unification variable, e.g. the result of an application.
 */
class TypeGraph {
    companion object {
        /** The absence of a node. */
        const val NONE = -1

        /** The label id of the arrow type constructor. */
        const val ARROW = -2

        private const val CTOR: Byte = 0
        private const val RIGID: Byte = 1
        private const val HOLE: Byte = 2
        private const val FRESH: Byte = 3

        /** Set on a class containing a [Blank] that may only ever become a label. */
        private const val LABEL_ONLY = 1

        // Journal opcodes. An entry is (op, a, b) packed into a Long.
        private const val UNION = 2
        private const val SET_CTOR = 3
        private const val SET_RIGID = 4
        private const val SET_HOLE = 5
        private const val SET_FLAGS = 6
        private const val SWAP_HOLES = 7
        private const val NEW_RIGID = 8
        private const val NEW_HOLE = 9
        private const val RETIRE_HOLE = 10
        private const val SET_NEXT = 11

        private const val FIELD = 30
        private const val MASK = (1L shl FIELD) - 1

        /** All journalled values are node indices or small counts, so all fit unsigned in [FIELD]. */
        private fun entry(op: Int, a: Int, b: Int) =
            (op.toLong() shl (2 * FIELD)) or ((a.toLong() and MASK) shl FIELD) or (b.toLong() and MASK)
    }

    // ---------------------------------------------------------------- node storage

    private var kind = ByteArray(64)

    /** CTOR: label id ([ARROW] for arrows). RIGID: variable id. */
    private var key = IntArray(64)

    /** RIGID, HOLE: the instantiation the node belongs to. */
    private var inst = IntArray(64)

    /** CTOR: where this node's arguments start in [args], and how many there are. */
    private var argOff = IntArray(64)
    private var argLen = IntArray(64)

    /** How long [args] was when this node was allocated, so a rewind can truncate it. */
    private var argsAt = IntArray(64)

    /** HOLE: the hole this node instantiates, needed to report constraints back to the search. */
    private var holeOf = arrayOfNulls<THole>(64)

    // ------------------------------------------------------- class state (valid at roots)

    private var parent = IntArray(64)
    private var classSize = IntArray(64)
    private var ctorAt = IntArray(64)
    private var rigidAt = IntArray(64)
    private var holeAt = IntArray(64)

    /** The HOLE nodes of a class, as a circular list, so two lists splice in one swap. */
    private var nextHole = IntArray(64)
    private var flags = IntArray(64)

    /** Scratch for [occurs], stamped with [stamp] so it never needs clearing. */
    private var seen = IntArray(64)
    private var stamp = 0

    private var count = 0
    private val args = IntVec()
    private val trail = LongVec()
    private val pending = IntVec()
    private val stack = IntVec()

    /** `rigidNodes[instantiation][variable]`, or [NONE]; rows are allocated on demand. */
    private var rigidNodes = arrayOfNulls<IntArray>(16)

    /** Where one hole was instantiated, and whether a refinement has since replaced that hole. */
    private class Instances(val nodes: IntVec) {
        var live = true
    }

    private val holeInstances = HashMap<THole, Instances>()

    /** True once a merge has failed; cleared by rewinding past the failure. */
    var failed = false
        private set

    private var failedAt = 0

    /** The two labels whose mismatch caused the most recent failure, if that is what it was. */
    var clash: Set<Int> = emptySet()
        private set

    // ---------------------------------------------------------------- node construction

    private fun alloc(k: Byte): Int {
        if (count == kind.size) grow(count * 2)
        val n = count++
        argsAt[n] = args.size
        kind[n] = k
        parent[n] = n
        classSize[n] = 1
        ctorAt[n] = NONE
        rigidAt[n] = NONE
        holeAt[n] = NONE
        nextHole[n] = n
        flags[n] = 0
        holeOf[n] = null
        return n
    }

    private fun grow(n: Int) {
        kind = kind.copyOf(n)
        key = key.copyOf(n)
        inst = inst.copyOf(n)
        argOff = argOff.copyOf(n)
        argLen = argLen.copyOf(n)
        argsAt = argsAt.copyOf(n)
        holeOf = holeOf.copyOf(n)
        parent = parent.copyOf(n)
        classSize = classSize.copyOf(n)
        ctorAt = ctorAt.copyOf(n)
        rigidAt = rigidAt.copyOf(n)
        holeAt = holeAt.copyOf(n)
        nextHole = nextHole.copyOf(n)
        flags = flags.copyOf(n)
        seen = seen.copyOf(n)
    }

    fun freshVar(): Int = alloc(FRESH)

    /** The node for [Variable] [v] at instantiation [i]; shared by every occurrence of it. */
    fun rigid(v: Int, i: Int): Int {
        if (i >= rigidNodes.size) rigidNodes = rigidNodes.copyOf(maxOf(i + 1, rigidNodes.size * 2))
        var row = rigidNodes[i]
        if (row == null || v >= row.size) {
            row = IntArray(maxOf(v + 1, 8)) { NONE }.also { rigidNodes[i]?.copyInto(it) }
            rigidNodes[i] = row
        }
        if (row[v] != NONE) return row[v]
        val n = alloc(RIGID)
        key[n] = v
        inst[n] = i
        rigidAt[n] = n
        row[v] = n
        trail.add(entry(NEW_RIGID, i, v))
        return n
    }

    /** A new node for [hole] at instantiation [i]. Each pair occurs at most once. */
    fun hole(hole: THole, i: Int): Int {
        val n = alloc(HOLE)
        inst[n] = i
        holeOf[n] = hole
        holeAt[n] = n
        if (hole is Blank && hole.labelOnly) flags[n] = LABEL_ONLY
        val instances = holeInstances[hole]
        if (instances == null) {
            holeInstances[hole] = Instances(IntVec(4).also { it.add(n) })
            trail.add(entry(NEW_HOLE, n, 0))
        } else instances.nodes.add(n)
        return n
    }

    fun ctor(label: Int, arguments: IntArray): Int {
        val n = alloc(CTOR)
        key[n] = label
        argOff[n] = args.size
        argLen[n] = arguments.size
        for (a in arguments) args.add(a)
        ctorAt[n] = n
        return n
    }

    fun arrow(from: Int, to: Int): Int {
        val n = alloc(CTOR)
        key[n] = ARROW
        argOff[n] = args.size
        argLen[n] = 2
        args.add(from, to)
        ctorAt[n] = n
        return n
    }

    /** The label of the constructor [node]'s class is known to have, or [NONE] if it has none. */
    fun constructorOf(node: Int): Int {
        val c = ctorAt[find(node)]
        return if (c == NONE) NONE else key[c]
    }

    /** How many arguments the constructor of [node]'s class takes. Requires it to have one. */
    fun constructorArity(node: Int) = argLen[ctorAt[find(node)]]

    /** The nodes instantiating [hole], in instantiation order, or null if it has been refined away. */
    fun instancesOf(hole: THole): IntVec? = holeInstances[hole]?.takeIf { it.live }?.nodes

    /** Forgets [hole], which a refinement has replaced with a type. */
    fun retireHole(hole: THole) {
        val instances = holeInstances[hole] ?: return
        if (!instances.live) return
        instances.live = false
        trail.add(entry(RETIRE_HOLE, instances.nodes[0], 0))
        for (i in 0 until instances.nodes.size) unlinkHole(instances.nodes[i])
    }

    /** Drops [n] from its class's list of holes, so only live holes are ever reported. */
    private fun unlinkHole(n: Int) {
        val root = find(n)
        var before = n
        while (nextHole[before] != n) before = nextHole[before]
        val after = nextHole[n]
        if (before != n) {
            trail.add(entry(SET_NEXT, before, nextHole[before]))
            nextHole[before] = after
            trail.add(entry(SET_NEXT, n, after))
            nextHole[n] = n
        }
        if (holeAt[root] == n) {
            trail.add(entry(SET_HOLE, root, holeAt[root] + 1))
            holeAt[root] = if (before == n) NONE else after
        }
    }

    /** Which instantiation of its component's type [node] belongs to. */
    fun instantiationOf(node: Int) = inst[node]

    // ---------------------------------------------------------------- union-find

    /**
     * The result of applying something of type [fn] to something of type [arg], or [NONE] if that
     * is a type error.
     */
    fun apply(fn: Int, arg: Int): Int {
        if (failed) return NONE
        val f = find(fn)
        val c = ctorAt[f]
        if (c != NONE) {
            if (key[c] != ARROW) {
                fail(trail.size)
                return NONE
            }
            return if (merge(args[argOff[c]], arg)) args[argOff[c] + 1] else NONE
        }
        val result = freshVar()
        return if (merge(f, arrow(arg, result))) result else NONE
    }

    fun find(x: Int): Int {
        var i = x
        while (parent[i] != i) i = parent[i]
        return i
    }

    /**
     * Unifies the types denoted by [a] and [b]. Returns false, and leaves [failed] set, if they are
     * incompatible; the caller is expected to rewind rather than to keep using the graph.
     */
    fun merge(a: Int, b: Int): Boolean {
        if (failed) return false
        clash = emptySet()
        val start = trail.size
        pending.clear()
        pending.add(a, b)
        while (!pending.isEmpty()) {
            val y = pending.removeLast()
            val x = pending.removeLast()
            val rx = find(x)
            val ry = find(y)
            if (rx == ry) continue
            val cx = ctorAt[rx]
            val cy = ctorAt[ry]
            if (cx != NONE && cy != NONE) {
                if (key[cx] != key[cy] || argLen[cx] != argLen[cy]) {
                    if (key[cx] != ARROW && key[cy] != ARROW) clash = setOf(key[cx], key[cy])
                    return fail(start)
                }
                for (i in 0 until argLen[cx]) pending.add(args[argOff[cx] + i], args[argOff[cy] + i])
            } else if (cx != NONE) {
                if (occurs(ry, cx)) return fail(start)
            } else if (cy != NONE) {
                if (occurs(rx, cy)) return fail(start)
            }
            if (!link(rx, ry)) return fail(start)
        }
        return true
    }

    private fun fail(start: Int): Boolean {
        failed = true
        failedAt = start
        return false
    }

    /**
     * Merges the class rooted at [x] into the one rooted at [y] (or the other way round; the larger
     * class wins). Returns false if the merged class is contradictory.
     */
    private fun link(x: Int, y: Int): Boolean {
        val big: Int
        val small: Int
        if (classSize[x] >= classSize[y]) {
            big = x
            small = y
        } else {
            big = y
            small = x
        }
        if (ctorAt[big] == NONE && ctorAt[small] != NONE) {
            trail.add(entry(SET_CTOR, big, ctorAt[big] + 1))
            ctorAt[big] = ctorAt[small]
        }
        val rigid = laterOf(rigidAt[big], rigidAt[small])
        if (rigid != rigidAt[big]) {
            trail.add(entry(SET_RIGID, big, rigidAt[big] + 1))
            rigidAt[big] = rigid
        }
        if (holeAt[small] != NONE) {
            if (holeAt[big] == NONE) {
                trail.add(entry(SET_HOLE, big, holeAt[big] + 1))
                holeAt[big] = holeAt[small]
            } else spliceHoles(holeAt[big], holeAt[small])
        }
        val merged = flags[big] or flags[small]
        if (merged != flags[big]) {
            trail.add(entry(SET_FLAGS, big, flags[big]))
            flags[big] = merged
        }
        trail.add(entry(UNION, small, 0))
        parent[small] = big
        classSize[big] += classSize[small]
        // A blank that stands for a label can never turn out to be a function.
        return (merged and LABEL_ONLY) == 0 || ctorAt[big] == NONE || key[ctorAt[big]] != ARROW
    }

    /**
     * Which of two rigid variables names the merged class. The later-instantiated one wins, so a
     * function's variables read back as the argument's rather than the other way round.
     */
    private fun laterOf(x: Int, y: Int): Int = when {
        x == NONE -> y
        y == NONE -> x
        inst[y] > inst[x] || (inst[y] == inst[x] && y > x) -> y
        else -> x
    }

    private fun spliceHoles(x: Int, y: Int) {
        trail.add(entry(SWAP_HOLES, x, y))
        val t = nextHole[x]
        nextHole[x] = nextHole[y]
        nextHole[y] = t
    }

    /** Whether the class [v] appears strictly inside the term rooted at constructor node [c]. */
    private fun occurs(v: Int, c: Int): Boolean {
        if (stamp == Int.MAX_VALUE) {
            seen.fill(0)
            stamp = 0
        }
        stamp++
        stack.clear()
        for (i in 0 until argLen[c]) stack.add(args[argOff[c] + i])
        while (!stack.isEmpty()) {
            val r = find(stack.removeLast())
            if (r == v) return true
            if (seen[r] == stamp) continue
            seen[r] = stamp
            val inner = ctorAt[r]
            if (inner != NONE) for (i in 0 until argLen[inner]) stack.add(args[argOff[inner] + i])
        }
        return false
    }

    // ---------------------------------------------------------------- undo

    /**
     * Runs [body] as if nothing had failed yet, then restores the graph exactly. Used to type an
     * expression that is not part of the checked program.
     */
    fun <T> speculate(body: () -> T): T {
        val mark = mark()
        val wasFailed = failed
        val wasFailedAt = failedAt
        val wasClash = clash
        failed = false
        val result = body()
        rewindTo(mark)
        failed = wasFailed
        failedAt = wasFailedAt
        clash = wasClash
        return result
    }

    /** A point to which the graph can later be [rewindTo]. */
    fun mark(): Long = (trail.size.toLong() shl 32) or count.toLong()

    /** Undoes everything done since [mark] was taken. */
    fun rewindTo(mark: Long) {
        val journalled = (mark ushr 32).toInt()
        while (trail.size > journalled) {
            val e = trail.removeLast()
            val a = ((e ushr FIELD) and MASK).toInt()
            val b = (e and MASK).toInt()
            when ((e ushr (2 * FIELD)).toInt()) {
                UNION -> {
                    classSize[parent[a]] -= classSize[a]
                    parent[a] = a
                }
                SET_CTOR -> ctorAt[a] = b - 1
                SET_RIGID -> rigidAt[a] = b - 1
                SET_HOLE -> holeAt[a] = b - 1
                SET_FLAGS -> flags[a] = b
                SET_NEXT -> nextHole[a] = b
                SWAP_HOLES -> {
                    val t = nextHole[a]
                    nextHole[a] = nextHole[b]
                    nextHole[b] = t
                }
                NEW_RIGID -> rigidNodes[a]!![b] = NONE
                NEW_HOLE -> holeInstances.remove(holeOf[a])
                RETIRE_HOLE -> holeInstances[holeOf[a]]!!.live = true
            }
        }
        if (failed && failedAt >= journalled) failed = false
    }

    // ---------------------------------------------------------------- reading types back out

    /**
     * The type denoted by [node], as far as unification has determined it. An unconstrained class
     * reads back as [Bottom]: the search treats that as "no information", which is what it is.
     *
     * @param ignoring a hole node whose own identity should not be reported as a constraint on
     *   itself.
     */
    fun typeAt(node: Int, ignoring: Int = NONE): ConstraintTy {
        val r = find(node)
        val c = ctorAt[r]
        if (c != NONE) {
            val off = argOff[c]
            return if (key[c] == ARROW) ConstraintArrow(typeAt(args[off]), typeAt(args[off + 1]))
            else ConstraintLabel(key[c], List(argLen[c]) { typeAt(args[off + it]) })
        }
        val v = rigidAt[r]
        if (v != NONE) return ConstraintVariable(key[v], inst[v])
        val h = liveHoleIn(r, ignoring)
        if (h != NONE) return InstantiationTy(holeOf[h]!!, inst[h])
        return Bottom
    }

    /**
     * What unification learned about the hole instance [node], or null if it was never unified with
     * anything and so is unconstrained.
     */
    fun constraintOn(node: Int): ConstraintTy? =
        if (classSize[find(node)] > 1) typeAt(node, ignoring = node) else null

    /**
     * Whether the check leaned on any live hole standing for something in particular. Being equal
     * to an unconstrained variable is not such a constraint — a variable accepts anything — but
     * having a constructor, or having to agree with a second hole, is.
     */
    fun anyHoleConstrained(): Boolean {
        for (instances in holeInstances.values) {
            if (!instances.live) continue
            val nodes = instances.nodes
            for (i in 0 until nodes.size) {
                val node = nodes[i]
                val root = find(node)
                if (ctorAt[root] != NONE || liveHoleIn(root, ignoring = node) != NONE) return true
            }
        }
        return false
    }

    /** A hole node in the class rooted at [root] other than [ignoring], if there is one. */
    private fun liveHoleIn(root: Int, ignoring: Int): Int {
        val start = holeAt[root]
        if (start == NONE) return NONE
        if (start != ignoring) return start
        val next = nextHole[start]
        return if (next == start) NONE else next
    }
}
