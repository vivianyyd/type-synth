package oneast

import util.IntVec

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
 * A node has no kind tag of its own. What it is, is which of its class's three slots it registered
 * itself in when it was allocated:
 * - [ctorAt] — an arrow or a label applied to argument nodes. Arrows are labels whose id is [ARROW].
 * - [rigidAt] — the instance of a component type's [Variable] at one instantiation.
 * - [holeAt] — the instance of a [THole] at one instantiation. Unifies like an ordinary variable;
 *   the types it ends up equal to are what [OneUnification.holeEquals] reports back to the search.
 *
 * A node in none of them ([freshVar]) is an anonymous unification variable, such as the result of
 * applying something whose type is not yet known to be a function. Every decision reads these three
 * slots at the class root, never anything about an individual node.
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

        /** Class root a's entry into its list of hole nodes changed from b. Undo: restore b. */
        private const val SET_HOLE = 3

        /** Class root a became marked as containing a label-only blank. Undo: clear the mark. */
        private const val SET_LABEL_ONLY = 4

        /**
         * The hole lists through hole nodes a and b were joined, by swapping their next nodes.
         * Undo: swap back.
         */
        private const val SWAP_HOLES = 5

        /**
         * A type variable node was created for instantiation a. Undo: forget it, the last pair in
         * a's list.
         */
        private const val NEW_RIGID = 6

        /** Hole node a was created as its hole's first instance. Undo: forget the hole. */
        private const val NEW_HOLE = 7

        /**
         * Hole node a was created as a further instance of its hole. Undo: remove it from the
         * instances.
         */
        private const val ADD_INSTANCE = 8

        /** The hole of instance node a was filled. Undo: the hole is unfilled again. */
        private const val RETIRE_HOLE = 9

        /** Hole node a's next node in its hole list changed from b. Undo: restore b. */
        private const val SET_NEXT = 10

        /** Unification failed. Undo: it has not failed. */
        private const val FAILED = 11
    }

    // ---------------------------------------------------------------- node storage

    /** CTOR: label id ([ARROW] for arrows). RIGID: variable id. */
    private var key = IntArray(INITIAL_NODES)

    /** RIGID, HOLE: the instantiation the node belongs to. */
    private var inst = IntArray(INITIAL_NODES)

    /** CTOR: where this node's arguments start in [args], and how many there are. */
    private var argOff = IntArray(INITIAL_NODES)
    private var argLen = IntArray(INITIAL_NODES)

    /** HOLE: the hole this node instantiates, needed to report constraints back to the search. */
    private var holeOf = arrayOfNulls<THole>(INITIAL_NODES)

    // ------------------------------------------------------- class state (valid at roots)

    private var parent = IntArray(INITIAL_NODES)
    private var classSize = IntArray(INITIAL_NODES)
    private var ctorAt = IntArray(INITIAL_NODES)
    private var rigidAt = IntArray(INITIAL_NODES)
    private var holeAt = IntArray(INITIAL_NODES)

    /** The HOLE nodes of a class, as a circular list, so two lists splice in one swap. */
    private var nextHole = IntArray(INITIAL_NODES)

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

    /** Where one hole was instantiated, and whether a refinement has since replaced that hole. */
    private class Instances(val nodes: IntVec) {
        var live = true
    }

    private val holeInstances = HashMap<THole, Instances>()

    /** True once a merge has failed; cleared by rewinding past the failure. */
    var failed = false
        private set

    /** The two labels whose mismatch caused the most recent failure, if that is what it was. */
    var clash: Set<Int> = emptySet()
        private set

    // ---------------------------------------------------------------- node construction

    /** A new node, alone in its own class, with nothing known about it yet. */
    private fun alloc(): Int {
        if (count == parent.size) grow(count * 2)
        val n = count++
        parent[n] = n
        classSize[n] = 1
        ctorAt[n] = NONE
        rigidAt[n] = NONE
        holeAt[n] = NONE
        nextHole[n] = n
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
        holeAt = holeAt.copyOf(n)
        nextHole = nextHole.copyOf(n)
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

    /** A new node for [hole] at instantiation [i]. Each pair occurs at most once. */
    fun hole(hole: THole, i: Int): Int {
        val n = alloc()
        inst[n] = i
        holeOf[n] = hole
        holeAt[n] = n
        labelOnly[n] = hole is Blank && hole.labelOnly
        val instances = holeInstances[hole]
        if (instances == null) {
            holeInstances[hole] = Instances(IntVec(SHORT_LIST).also { it.add(n) })
            log(NEW_HOLE, n)
        } else {
            instances.nodes.add(n)
            log(ADD_INSTANCE, n)
        }
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

    /**
     * The nodes instantiating [hole], in instantiation order, or null if it has been refined away.
     */
    fun instancesOf(hole: THole): IntVec? = holeInstances[hole]?.takeIf { it.live }?.nodes

    /** Forgets [hole], which a refinement has replaced with a type. */
    fun retireHole(hole: THole) {
        val instances = holeInstances[hole] ?: return
        if (!instances.live) return
        instances.live = false
        log(RETIRE_HOLE, instances.nodes[0])
        for (i in 0 until instances.nodes.size) unlinkHole(instances.nodes[i])
    }

    /** Drops [n] from its class's list of holes, so only live holes are ever reported. */
    private fun unlinkHole(n: Int) {
        val root = find(n)
        var before = n
        while (nextHole[before] != n) before = nextHole[before]
        val after = nextHole[n]
        if (before != n) {
            log(SET_NEXT, before, nextHole[before])
            nextHole[before] = after
            log(SET_NEXT, n, after)
            nextHole[n] = n
        }
        if (holeAt[root] == n) {
            log(SET_HOLE, root, holeAt[root])
            holeAt[root] = if (before == n) NONE else after
        }
    }

    /** Which instantiation of its component's type [node] belongs to. */
    fun instantiationOf(node: Int) = inst[node]

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
        if (holeAt[small] != NONE) {
            if (holeAt[big] == NONE) {
                log(SET_HOLE, big, holeAt[big])
                holeAt[big] = holeAt[small]
            } else spliceHoles(holeAt[big], holeAt[small])
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

    private fun spliceHoles(x: Int, y: Int) {
        log(SWAP_HOLES, x, y)
        val t = nextHole[x]
        nextHole[x] = nextHole[y]
        nextHole[y] = t
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

    /** A point to which the graph can later be [rewindTo]: the length of the journal. */
    fun mark(): Int = journalOp.size

    /**
     * Undoes everything done since [mark] was taken, newest first, as each opcode describes.
     */
    fun rewindTo(mark: Int) {
        while (journalOp.size > mark) {
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
                SET_HOLE -> holeAt[a] = b
                SET_LABEL_ONLY -> labelOnly[a] = false
                SET_NEXT -> nextHole[a] = b
                SWAP_HOLES -> {
                    val t = nextHole[a]
                    nextHole[a] = nextHole[b]
                    nextHole[b] = t
                }
                NEW_RIGID -> rigidNodes[a]!!.run {
                    removeLast()
                    removeLast()
                }
                NEW_HOLE -> holeInstances.remove(holeOf[a])
                RETIRE_HOLE -> holeInstances[holeOf[a]]!!.live = true
                ADD_INSTANCE -> holeInstances[holeOf[a]]!!.nodes.removeLast()
                FAILED -> failed = false
            }
        }
    }

    // ---------------------------------------------------------------- reading types back out

    /**
     * The type denoted by [node], as far as unification has determined it. A class reads back as
     * the first of these it has: a constructor; a hole; a type variable; otherwise [Bottom].
     *
     * Holes outrank variables because the search groups holes by what they are equal to: two holes
     * in one class must be filled the same way, and reporting a variable they share would hide that.
     *
     */
    fun typeAt(node: Int): ConstraintTy = typeAt(node, ignoring = NONE)

    /** [typeAt], but never reporting the hole node [ignoring] as what its own class is equal to. */
    private fun typeAt(node: Int, ignoring: Int): ConstraintTy {
        val r = find(node)
        val c = ctorAt[r]
        if (c != NONE) {
            val off = argOff[c]
            return if (key[c] == ARROW) ConstraintArrow(typeAt(args[off]), typeAt(args[off + 1]))
            else ConstraintLabel(key[c], List(argLen[c]) { typeAt(args[off + it]) })
        }
        val h = liveHoleIn(r, ignoring)
        if (h != NONE) return InstantiationTy(holeOf[h]!!, inst[h])
        val v = rigidAt[r]
        if (v != NONE) return ConstraintVariable(key[v], inst[v])
        return Bottom
    }

    /**
     * What unification learned about the hole instance [node]: its class's constructor, another
     * hole in its class, or a type variable in its class. Null if the class has none of those.
     *
     * A class that holds only this hole and anonymous variables says nothing, and whether it holds
     * any anonymous variables at all depends on the order holes were filled in. So it is reported
     * as nothing, rather than as [Bottom].
     */
    fun constraintOn(node: Int): ConstraintTy? {
        val r = find(node)
        val known = ctorAt[r] != NONE || liveHoleIn(r, ignoring = node) != NONE || rigidAt[r] != NONE
        return if (known) typeAt(node, ignoring = node) else null
    }

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

    /** A hole node in the class rooted at [root] other than [ignoring], if there is one. */
    private fun liveHoleIn(root: Int, ignoring: Int): Int {
        val start = holeAt[root]
        if (start == NONE) return NONE
        if (start != ignoring) return start
        val next = nextHole[start]
        return if (next == start) NONE else next
    }
}
