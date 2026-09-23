package oneast.unit

import oneast.*
import org.junit.jupiter.api.Test
import query.App
import query.Name
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertFalse
import kotlin.test.assertTrue

/** The journal must restore the graph exactly, including whether unification had failed. */
class RewindTest {
    /** A failure that wrote nothing to the journal sits at the same position as the state before it. */
    @Test
    fun `failure survives a rewind to where it happened`() {
        val graph = TypeGraph()
        val x = graph.ctor(0, IntArray(0))
        val y = graph.ctor(1, IntArray(0))
        assertFalse(graph.merge(x, y))
        assertTrue(graph.failed)
        val here = graph.mark()
        graph.rewindTo(here)
        assertTrue(graph.failed, "rewinding to a point after the failure must not clear it")
    }

    /**
     * Undoing the recorded changes is not enough: allocating a node records nothing to undo, so a
     * rewind has to drop the nodes too or an abandoned branch is kept forever.
     */
    @Test
    fun `a rewind gives the nodes back`() {
        val graph = TypeGraph()
        val outer = graph.ctor(0, IntArray(0))
        val before = graph.nodes
        val mark = graph.mark()
        val hole = graph.hole(TypeHole(), 0)
        graph.merge(hole, graph.ctor(1, intArrayOf(graph.arrow(outer, graph.freshVar()))))
        assertTrue(graph.nodes > before, "the merge should have allocated something")
        graph.rewindTo(mark)
        assertEquals(before, graph.nodes, "a rewind must drop what it undid")
        assertTrue(graph.acyclic())
        // And the reused slots behave like new ones.
        val again = graph.hole(TypeHole(), 0)
        assertEquals(before, again, "the next node should reuse the slot just freed")
        assertTrue(graph.merge(again, outer))
    }

    /** Rewinding twice to the same mark is what the enumerator does for each sibling expansion. */
    @Test
    fun `rewinding to the same mark twice is allowed, rewinding forward is not`() {
        val graph = TypeGraph()
        val mark = graph.mark()
        graph.merge(graph.freshVar(), graph.ctor(0, IntArray(0)))
        graph.rewindTo(mark)
        val stale = graph.mark()
        graph.freshVar()
        graph.rewindTo(stale)
        graph.rewindTo(stale)
        assertEquals(0, graph.nodes)
        graph.freshVar()
        val deeper = graph.mark()
        graph.freshVar()
        graph.rewindTo(mark)
        assertFailsWith<IllegalStateException> { graph.rewindTo(deeper) }
    }

    @Test
    fun `typing an expression does not disturb the check`() {
        val hole = TypeHole()
        val I = NamedLabel(0, listOf())
        val context = SearchState(
            names = mapOf("f" to 0, "x" to 1),
            types = listOf(Arrow(hole, I), I),
            labelArities = mapOf(0 to 0)
        )
        val example = App(Name("f"), Name("x"))
        val u = OneUnification(context, listOf(example))
        val before = u.holeConstructor(hole) to u.classesOf(hole).toList()
        u.type(example)
        assertEquals(before, u.holeConstructor(hole) to u.classesOf(hole).toList())
    }
}
