package oneast

import util.IntVec

/**
 * A store of type terms under syntactic unification, with an undo journal.
 *
 * Terms are nodes, identified by [Int]. A node's own shape never changes; what changes is which
 * nodes are known to denote the same type, which is tracked by union-find. Each *class* (union-find
 * root) remembers the constructor and the type variable it contains, so a merge only has to look at
 * the two roots.
 *
 * Every write is journalled, so [rewindTo] restores an earlier state exactly. That is what makes
 * checking a refinement cheap: a child search state differs from its parent only in that one hole
 * has grown into a type, so it can be checked by merging that growth into the parent's graph
 * (O(occurrences of the hole)) rather than re-deriving the whole thing (O(size of all examples)).
 *
 * A node is one of:
 * - a constructor: an arrow or a label applied to argument nodes. Arrows are labels whose id is
 *   [ARROW].
 * - a type variable of a component's type, at one instantiation. See [rigid].
 * - a hole of a component's type, at one instantiation. It unifies like an ordinary variable. See
 *   [hole].
 * - an anonymous variable ([freshVar]), such as the result of applying something whose type is not
 *   yet known to be a function.
 */
class TypeGraph {
    private enum class Visit { UNVISITED, ON_PATH, DONE }

    companion object {
        /** Stored where a node is expected but there is none. */
        private const val NONE = -1

        /** The label id stored for the arrow type constructor. Label ids are never negative. */
        private const val ARROW = -2

        /** Starting length of the per-node arrays. They double whenever they fill up. */
        private const val INITIAL_NODES = 64

        /**
         * Starting length of [rigidNodes], which has a slot per instantiation and grows as needed.
         */
        private const val INITIAL_INSTANTIATIONS = 16

        /**
         * Starting capacity of the lists kept per hole (its instances) and per instantiation (its
         * type variables). Most have only a few entries; the lists grow if not.
         */
        private const val SHORT_LIST = 4

        // Journal opcodes. A journal entry is an opcode and two values, a and b, which are 0 when
        // the opcode does not use them. Each opcode below records one kind of change, and says what
        // a and b hold and what undoing the change does.

        /**
         * Class root a was merged into another class. Undo: a is a root again, with its own size.
         */
        private const val UNION = 0

        /**
         * Class root a gained a constructor; b is what it had before, always NONE. Undo: restore b.
         */
        private const val SET_CTOR = 1

        /**
         * Class root a gained a type variable; b is what it had before, always NONE. Undo: restore b.
         */
        private const val SET_RIGID = 2

        /** Class root a became marked as containing a label-only blank. Undo: clear the mark. */
        private const val SET_LABEL_ONLY = 3

        /**
         * A type variable node was created for instantiation a. Undo: forget it, the last pair in
         * a's list.
         */
        private const val NEW_RIGID = 4

        /**
         * Hole node a was created as an instance of its hole. Undo: remove it from the hole's
         * instances, and forget the hole if that leaves none.
         */
        private const val NEW_INSTANCE = 5

        /** Unification failed. Undo: it has not failed. */
        private const val FAILED = 6
    }

    // ---------------------------------------------------------------- node storage

    /** For a constructor, its label id ([ARROW] for arrows). For a type variable, its id. */
    private var key = IntArray(INITIAL_NODES)

    /** For a type variable or hole node, the instantiation it belongs to. */
    private var inst = IntArray(INITIAL_NODES)

    /** For a constructor: where its arguments start in [args], and how many there are. */
    private var argOff = IntArray(INITIAL_NODES)
    private var argLen = IntArray(INITIAL_NODES)

    /** For a hole node, the hole it instantiates. */
    private var holeOf = arrayOfNulls<THole>(INITIAL_NODES)

    // ------------------------------------------------------- class state (valid at roots)

    private var parent = IntArray(INITIAL_NODES)
    private var classSize = IntArray(INITIAL_NODES)
    private var ctorAt = IntArray(INITIAL_NODES)
    private var rigidAt = IntArray(INITIAL_NODES)

    /** Whether a class contains a [Blank] that may only ever become a label. */
    private var labelOnly = BooleanArray(INITIAL_NODES)

    /** Scratch for [occurs], stamped with [stamp] so it never needs clearing. */
    private var seen = IntArray(INITIAL_NODES)
    private var stamp = 0

    private var count = 0
    private val args = IntVec()

    /** The journal: one entry per change, as three parallel columns. */
    private val journalOp = IntVec()
    private val journalA = IntVec()
    private val journalB = IntVec()

    private val pending = IntVec()
    private val stack = IntVec()

    /** For each instantiation, the nodes of its type variables, as (variable, node) pairs. */
    private var rigidNodes = arrayOfNulls<IntVec>(INITIAL_INSTANTIATIONS)

    /** The nodes instantiating each hole, in the order they were created. */
    private val holeInstances = HashMap<THole, IntVec>()

    /** True once a merge has failed; cleared by rewinding past the failure. */
    var failed = false
        private set

    /** The two labels whose mismatch caused the most recent failure, if that is what it was. */
    var clash: Set<Int> = emptySet()
        private set

    /**
     * A point the graph can be [rewindTo]. It is a journal position, plus the number of nodes and
     * of constructor arguments there were when it was taken: undoing the recorded changes is not
     * enough on its own, because allocating a node records nothing to undo.
     */
    class Mark internal constructor(
        internal val journal: Int,
        internal val nodes: Int,
        internal val args: Int,
    )

    /** How many nodes the graph holds. For tests and for diagnosing memory use. */
    val nodes: Int
        get() = count

    // ---------------------------------------------------------------- node construction

    /** A new node, alone in its own class, with nothing known about it yet. */
    private fun alloc(): Int {
        if (count == parent.size) grow(count * 2)
        val n = count++
        parent[n] = n
        classSize[n] = 1
        ctorAt[n] = NONE
        rigidAt[n] = NONE
        labelOnly[n] = false
        holeOf[n] = null
        return n
    }

    private fun grow(n: Int) {
        key = key.copyOf(n)
        inst = inst.copyOf(n)
        argOff = argOff.copyOf(n)
        argLen = argLen.copyOf(n)
        holeOf = holeOf.copyOf(n)
        parent = parent.copyOf(n)
        classSize = classSize.copyOf(n)
        ctorAt = ctorAt.copyOf(n)
        rigidAt = rigidAt.copyOf(n)
        labelOnly = labelOnly.copyOf(n)
        seen = seen.copyOf(n)
    }

    fun freshVar(): Int = alloc()

    /** The node for [Variable] [v] at instantiation [i]; shared by every occurrence of it. */
    fun rigid(v: Int, i: Int): Int {
        if (i >= rigidNodes.size) rigidNodes = rigidNodes.copyOf(maxOf(i + 1, rigidNodes.size * 2))
        val pairs = rigidNodes[i] ?: IntVec(SHORT_LIST).also { rigidNodes[i] = it }
        // Pairs are stored flat: the variable at even positions, its node right after it.
        for (k in 0 until pairs.size step 2) if (pairs[k] == v) return pairs[k + 1]
        val n = alloc()
        key[n] = v
        inst[n] = i
        rigidAt[n] = n
        pairs.add(v, n)
        log(NEW_RIGID, i)
        return n
    }

    /** A new node for [hole] at instantiation [i]. */
    fun hole(hole: THole, i: Int): Int {
        val n = alloc()
        inst[n] = i
        holeOf[n] = hole
        labelOnly[n] = hole is Blank && hole.labelOnly
        holeInstances.getOrPut(hole) { IntVec(SHORT_LIST) }.add(n)
        log(NEW_INSTANCE, n)
        return n
    }

    fun ctor(label: Int, arguments: IntArray): Int {
        val n = alloc()
        key[n] = label
        argOff[n] = args.size
        argLen[n] = arguments.size
        for (a in arguments) args.add(a)
        ctorAt[n] = n
        return n
    }

    fun arrow(from: Int, to: Int): Int {
        val n = alloc()
        key[n] = ARROW
        argOff[n] = args.size
        argLen[n] = 2 // an arrow's arguments are what it takes, then what it returns
        args.add(from, to)
        ctorAt[n] = n
        return n
    }

    /** The nodes instantiating [hole], or null if it has none. */
    fun instancesOf(hole: THole): IntVec? = holeInstances[hole]

    /** Which instantiation of its component's type [node] belongs to. */
    fun instantiationOf(node: Int) = inst[node]

    /** Whether [node]'s class is known to have a constructor. */
    fun hasConstructor(node: Int) = ctorAt[find(node)] != NONE

    /** Whether the constructor of [node]'s class is an arrow. Requires it to have one. */
    fun isArrow(node: Int) = key[ctorAt[find(node)]] == ARROW

    /** The label of the constructor of [node]'s class. Requires it to be a label. */
    fun labelOf(node: Int) = key[ctorAt[find(node)]]

    /**
     * Whether the classes of [x] and [y] have the same constructor with the same number of
     * arguments.
     */
    fun sameConstructor(x: Int, y: Int): Boolean {
        val cx = ctorAt[find(x)]
        val cy = ctorAt[find(y)]
        return key[cx] == key[cy] && argLen[cx] == argLen[cy]
    }

    // ---------------------------------------------------------------- union-find

    /**
     * The result of applying something of type [fn] to something of type [arg], or null if that is
     * a type error.
     */
    fun apply(fn: Int, arg: Int): Int? {
        if (failed) return null
        val f = find(fn)
        val c = ctorAt[f]
        if (c != NONE) {
            if (key[c] != ARROW) {
                fail()
                return null
            }
            // The arrow's first argument is what it takes, and its second is what it returns.
            return if (merge(args[argOff[c]], arg)) args[argOff[c] + 1] else null
        }
        val result = freshVar()
        return if (merge(f, arrow(arg, result))) result else null
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
                    return fail()
                }
                for (i in 0 until argLen[cx]) pending.add(args[argOff[cx] + i], args[argOff[cy] + i])
            }
            if (!link(rx, ry)) return fail()
        }
        return true
    }

    /**
     * Records a type error. Journalled rather than remembered as a position, because a merge can
     * fail without having written anything, and then the state before the failure and the state
     * after it are the same position — so a rewind to that position could not tell them apart.
     */
    private fun fail(): Boolean {
        log(FAILED)
        failed = true
        return false
    }

    /**
     * Merges the class rooted at [x] into the one rooted at [y] (or the other way round; the larger
     * class wins). Returns false if the merged class is contradictory.
     *
     * **Invariant: no class reaches itself through its constructor's arguments** — see [acyclic].
     * A class that did would denote an infinite type, which is never a solution. Merging is the
     * only thing that can break the invariant, and this is the argument that it does not:
     *
     * The merged class's arguments are those of whichever constructor survives. Every other class
     * keeps the arguments it had; all that changes is that an argument which was [x] or [y] is now
     * the merged class. So a cycle that did not exist before must run through the merged class,
     * which is to say there is a path from the surviving constructor's arguments back to [x] or to
     * [y]. Rejecting exactly that therefore preserves the invariant, and since a graph starts empty
     * it holds throughout.
     *
     * Checking where a variable class meets a constructor class is *not* enough. Merging two
     * classes that both already carry a constructor attaches one class's constructor to a class
     * that now also contains the other, which is equally a way for a class to end up below itself,
     * and class size decides which half that is. A unifier that builds an explicit substitution
     * escapes this: there, structure enters only when a variable is bound, so one check per
     * binding covers every case.
     *
     * The check runs before any write, so a rejected merge leaves nothing behind and the invariant
     * holds even while a failed [merge] is unwinding.
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
        val ctor = if (ctorAt[big] != NONE) ctorAt[big] else ctorAt[small]
        if (ctor != NONE && occurs(big, small, ctor)) return false

        if (ctorAt[big] == NONE && ctorAt[small] != NONE) {
            log(SET_CTOR, big, ctorAt[big])
            ctorAt[big] = ctorAt[small]
        }
        if (rigidAt[big] == NONE && rigidAt[small] != NONE) {
            log(SET_RIGID, big, rigidAt[big])
            rigidAt[big] = rigidAt[small]
        }
        if (labelOnly[small] && !labelOnly[big]) {
            log(SET_LABEL_ONLY, big)
            labelOnly[big] = true
        }
        log(UNION, small)
        parent[small] = big
        classSize[big] += classSize[small]
        // A blank that stands for a label can never turn out to be a function.
        return !labelOnly[big] || ctorAt[big] == NONE || key[ctorAt[big]] != ARROW
    }

    /** Whether class [v] or class [w] appears strictly inside the term rooted at [c]. */
    private fun occurs(v: Int, w: Int, c: Int): Boolean {
        // Every call uses a new stamp, so marks left by earlier calls never match. On the rare
        // wrap-around, clear the marks and start again from 1.
        if (stamp == Int.MAX_VALUE) {
            seen.fill(0)
            stamp = 0
        }
        stamp++
        stack.clear()
        for (i in 0 until argLen[c]) stack.add(args[argOff[c] + i])
        while (!stack.isEmpty()) {
            val r = find(stack.removeLast())
            if (r == v || r == w) return true
            if (seen[r] == stamp) continue
            seen[r] = stamp
            val inner = ctorAt[r]
            if (inner != NONE) for (i in 0 until argLen[inner]) stack.add(args[argOff[inner] + i])
        }
        return false
    }

    // ---------------------------------------------------------------- undo

    /** Appends a journal entry. See the opcodes for what [a] and [b] mean for each. */
    private fun log(op: Int, a: Int = 0, b: Int = 0) {
        journalOp.add(op)
        journalA.add(a)
        journalB.add(b)
    }

    /** A point to which the graph can later be [rewindTo]. */
    fun mark(): Mark = Mark(journalOp.size, count, args.size)

    /**
     * Undoes everything done since [mark] was taken, newest first, as each opcode describes, and
     * then drops the nodes and constructor arguments allocated since then.
     *
     * Dropping them is sound because nothing that survives the undo can point at them. A node
     * index is stored in exactly two kinds of place. Either the write is journalled and has just
     * been undone — [parent] by `UNION`, [ctorAt] by `SET_CTOR`, [rigidAt] by `SET_RIGID`,
     * [rigidNodes] by `NEW_RIGID`, [holeInstances] by `NEW_INSTANCE` — or it was written once when
     * the *referring* node was allocated and is never touched again: a node's own slot on its
     * class, its [argOff]/[argLen], and its arguments in [args]. A write of the second kind can
     * only name nodes that already existed, so a node allocated before the mark never names one
     * allocated after it. The remaining node indices live in [pending] and [stack], which are
     * cleared by whatever is using them, and no caller holds one across a rewind.
     *
     * So this does not over-delete: every node it drops is unreachable, and it drops nothing that
     * existed at [mark].
     */
    fun rewindTo(mark: Mark) {
        check(mark.journal <= journalOp.size && mark.nodes <= count && mark.args <= args.size) {
            "This mark has already been rewound past; the state it named is gone."
        }
        while (journalOp.size > mark.journal) {
            val op = journalOp.removeLast()
            val a = journalA.removeLast()
            val b = journalB.removeLast()
            when (op) {
                UNION -> {
                    classSize[parent[a]] -= classSize[a]
                    parent[a] = a
                }
                SET_CTOR -> ctorAt[a] = b
                SET_RIGID -> rigidAt[a] = b
                SET_LABEL_ONLY -> labelOnly[a] = false
                NEW_RIGID -> rigidNodes[a]!!.run {
                    removeLast()
                    removeLast()
                }
                NEW_INSTANCE -> {
                    val hole = holeOf[a]!!
                    val instances = holeInstances.getValue(hole)
                    instances.removeLast()
                    if (instances.isEmpty()) holeInstances.remove(hole)
                }
                FAILED -> failed = false
            }
        }
        // Only holeOf has to be cleared: it is the one column holding references, so it is the one
        // that would keep a THole of an abandoned branch alive. Reusing a slot reinitialises the
        // rest of what is read about a node.
        holeOf.fill(null, mark.nodes, count)
        count = mark.nodes
        args.truncateTo(mark.args)
    }

    // ---------------------------------------------------------------- reading types back out

    /**
     * The type denoted by [node], as far as unification has determined it: its class's constructor,
     * else its type variable, else [Bottom].
     */
    fun typeAt(node: Int): ConstraintTy {
        val r = find(node)
        val c = ctorAt[r]
        if (c != NONE) {
            val off = argOff[c]
            return if (key[c] == ARROW) ConstraintArrow(typeAt(args[off]), typeAt(args[off + 1]))
            else ConstraintLabel(key[c], List(argLen[c]) { typeAt(args[off + it]) })
        }
        val v = rigidAt[r]
        return if (v != NONE) ConstraintVariable(key[v], inst[v]) else Bottom
    }

    /**
     * Whether no class reaches itself through its constructor's arguments — the invariant [link]
     * maintains, and which [merge] therefore never has to check for globally. Not used in the
     * search; it is here to be stated and tested.
     */
    fun acyclic(): Boolean {
        val visit = Array(count) { Visit.UNVISITED }
        fun walk(root: Int): Boolean =
            when (visit[root]) {
                Visit.ON_PATH -> false
                Visit.DONE -> true
                Visit.UNVISITED -> {
                    visit[root] = Visit.ON_PATH
                    val c = ctorAt[root]
                    val ok = c == NONE || (0 until argLen[c]).all { walk(find(args[argOff[c] + it])) }
                    visit[root] = Visit.DONE
                    ok
                }
            }
        for (n in 0 until count) if (!walk(find(n))) return false
        return true
    }
}
