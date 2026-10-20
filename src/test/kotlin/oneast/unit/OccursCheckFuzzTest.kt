package oneast.unit

import oneast.TypeGraph
import org.junit.jupiter.api.Test
import kotlin.random.Random
import kotlin.test.assertEquals
import kotlin.test.assertTrue
import kotlin.test.fail

/**
 * [TypeGraph.merge] must accept exactly the equations two independent references accept: a
 * substitution unifier with an occurs check per binding, and a union-find unifier with one global
 * acyclicity check at the end. Every state the graph accepts must be [TypeGraph.acyclic].
 */
class OccursCheckFuzzTest {
    /** A term over the graph's nodes: a variable node, or a label applied to arguments. */
    private sealed class Term {
        data class V(val node: Int) : Term()
        data class C(val label: Int, val args: List<Term>) : Term()
    }

    /** Robinson unification with an occurs check, over an explicit substitution. */
    private class Reference {
        val subst = HashMap<Int, Term>()
        var occursFailed = false

        fun walk(t: Term): Term {
            var u = t
            while (u is Term.V) u = subst[u.node] ?: return u
            return u
        }

        fun occurs(v: Int, t: Term): Boolean =
            when (val u = walk(t)) {
                is Term.V -> u.node == v
                is Term.C -> u.args.any { occurs(v, it) }
            }

        fun unify(a: Term, b: Term): Boolean {
            val x = walk(a)
            val y = walk(b)
            if (x == y) return true
            if (x is Term.V) {
                if (occurs(x.node, y)) return false.also { occursFailed = true }
                subst[x.node] = y
                return true
            }
            if (y is Term.V) return unify(y, x)
            x as Term.C
            y as Term.C
            if (x.label != y.label || x.args.size != y.args.size) return false
            return x.args.indices.all { unify(x.args[it], y.args[it]) }
        }
    }

    /** A constructor node's label and argument nodes. Variables have none. */
    private class Shape(val label: Int, val args: IntArray)

    /**
     * Huet-style unification with no occurs check while merging, and one global acyclicity check at
     * the end. Classes are merged in a fixed direction (no union by size), and the final graph has
     * an edge from a class to the arguments of *every* constructor in it, not just one. Rebuilt
     * from scratch on each call, from the node shapes alone.
     */
    private class Global(private val shapes: List<Shape?>) {
        private val parent = IntArray(shapes.size) { it }
        private val rep = IntArray(shapes.size) { if (shapes[it] != null) it else -1 }

        /** Which kind of failure it was, if [solve] returned false. */
        var cyclic = false

        private fun find(x: Int): Int {
            var i = x
            while (parent[i] != i) i = parent[i]
            return i
        }

        private fun argsOf(n: Int) = shapes[n]!!.args.toList()

        fun solve(equations: List<Pair<Int, Int>>): Boolean {
            val pending = ArrayDeque(equations)
            while (pending.isNotEmpty()) {
                val (a, b) = pending.removeFirst()
                val ra = find(a)
                val rb = find(b)
                if (ra == rb) continue
                val ca = rep[ra]
                val cb = rep[rb]
                if (ca != -1 && cb != -1) {
                    val ta = shapes[ca]!!
                    val tb = shapes[cb]!!
                    if (ta.label != tb.label || ta.args.size != tb.args.size) return false
                    pending.addAll(argsOf(ca).zip(argsOf(cb)))
                }
                parent[ra] = rb
                if (rep[rb] == -1) rep[rb] = ca
            }
            // Global check: DFS over classes, with edges from every constructor node.
            val edges = HashMap<Int, MutableList<Int>>()
            for (n in shapes.indices)
                if (shapes[n] != null)
                    edges.getOrPut(find(n)) { ArrayList() }.addAll(argsOf(n).map { find(it) })
            val state = IntArray(shapes.size) // 0 unvisited, 1 on path, 2 done
            fun dfs(r: Int): Boolean {
                if (state[r] == 1) return false
                if (state[r] == 2) return true
                state[r] = 1
                val ok = edges[r].orEmpty().all { dfs(it) }
                state[r] = 2
                return ok
            }
            cyclic = !shapes.indices.all { dfs(find(it)) }
            return !cyclic
        }
    }

    @Test
    fun `references agree on hand-checked cases`() {
        // Nodes: 0 x, 1 y, 2 f(x), 3 g(x), 4 h(x, y), 5 h(y, g(x)), 6 g(y), 7 f(g(y)), 8 f(y)
        val f = 1
        val h = 2
        val g = 3
        val shapes = listOf(
            null, null, Shape(f, intArrayOf(0)), Shape(g, intArrayOf(0)), Shape(h, intArrayOf(0, 1)),
            Shape(h, intArrayOf(1, 3)), Shape(g, intArrayOf(1)), Shape(f, intArrayOf(6)),
            Shape(f, intArrayOf(1)),
        )
        val all = ArrayList<Term>()
        for ((i, sh) in shapes.withIndex())
            all.add(if (sh == null) Term.V(i) else Term.C(sh.label, sh.args.map { all[it] }))
        val cases = listOf(
            listOf(0 to 2) to false, // x = f(x)
            listOf(4 to 5) to false, // h(x, y) = h(y, g(x)), so x = g(x)
            listOf(2 to 7) to true, // f(x) = f(g(y))
            listOf(2 to 8, 0 to 3) to false, // x = y, then x = g(x)
            listOf(2 to 8, 4 to 5) to false, // x = y, then y = g(x)
            listOf(0 to 6, 1 to 3) to false, // x = g(y), y = g(x): cycle of length 2
            listOf(2 to 3) to false, // label clash
            listOf(0 to 1, 1 to 0) to true,
        )
        for ((eqs, expected) in cases) {
            val ref = Reference()
            assertEquals(expected, eqs.all { (p, q) -> ref.unify(all[p], all[q]) }, "robinson $eqs")
            assertEquals(expected, Global(shapes).solve(eqs), "global $eqs")
        }
    }

    private val arity = intArrayOf(0, 1, 2, 1, 2)

    @Test
    fun `merge agrees with both references and stays acyclic`() {
        var accepted = 0
        var rejected = 0
        var cyclic = 0
        for (seed in 0 until 3000) {
            val rnd = Random(seed)
            val graph = TypeGraph()
            val terms = ArrayList<Term>()
            val shapes = ArrayList<Shape?>()
            val history = ArrayList<Pair<Int, Int>>() // accepted merges
            fun node(): Int {
                // Mostly variables and small constructors over existing nodes, so that cycles are
                // easy to close and constructor-vs-constructor merges are common.
                if (terms.isEmpty() || rnd.nextInt(3) == 0) {
                    terms.add(Term.V(graph.freshVar()))
                    shapes.add(null)
                    return terms.size - 1
                }
                val label = rnd.nextInt(arity.size)
                val as_ = IntArray(arity[label]) { rnd.nextInt(terms.size) }
                val n = graph.ctor(label, as_)
                assertEquals(terms.size, n)
                terms.add(Term.C(label, as_.map { terms[it] }))
                shapes.add(Shape(label, as_))
                return n
            }
            repeat(4 + rnd.nextInt(8)) { node() }
            repeat(30) {
                if (rnd.nextInt(4) == 0) node()
                val a = rnd.nextInt(terms.size)
                val b = rnd.nextInt(terms.size)
                val mark = graph.mark()
                val nodesBefore = graph.nodes
                val ok = graph.merge(a, b)
                val ref = Reference()
                val refOk = (history + (a to b)).all { (p, q) -> ref.unify(terms[p], terms[q]) }
                val global = Global(shapes)
                val globalOk = global.solve(history + (a to b))
                if (ok != refOk || ok != globalOk)
                    fail("seed=$seed merge($a,$b): graph=$ok robinson=$refOk global=$globalOk history=$history")
                assertTrue(graph.acyclic(), "seed=$seed after merge($a,$b) ok=$ok")
                if (ok) {
                    accepted++
                    history.add(a to b)
                    // Read-back must terminate on every node.
                    for (n in terms.indices) graph.typeAt(n)
                } else {
                    rejected++
                    if (ref.occursFailed) cyclic++
                    graph.rewindTo(mark)
                    assertEquals(nodesBefore, graph.nodes)
                    assertTrue(!graph.failed && graph.acyclic(), "seed=$seed rewind")
                }
            }
        }
        println("accepted=$accepted rejected=$rejected byOccurs=$cyclic")
        assertTrue(cyclic > 500 && accepted > 1000, "accepted=$accepted rejected=$rejected")
    }
}
