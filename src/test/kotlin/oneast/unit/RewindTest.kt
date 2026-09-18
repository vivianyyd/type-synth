package oneast.unit

import oneast.*
import org.junit.jupiter.api.Test
import query.App
import query.Name
import kotlin.test.assertEquals
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

    /** type() instantiates the environment again, appending to holes that already have instances. */
    @Test
    fun `typing an expression does not disturb the recorded hole instances`() {
        val hole = TypeHole()
        val I = NamedLabel(0, listOf())
        val context = SearchState(
            names = mapOf("f" to 0, "x" to 1),
            types = listOf(Arrow(hole, I), I),
            labelArities = mapOf(0 to 0)
        )
        val example = App(Name("f"), Name("x"))
        val u = OneUnification(context, listOf(example))
        val before = u.holeEquals(hole)
        u.type(example)
        assertEquals(before, u.holeEquals(hole), "type() must leave the check as it found it")
    }
}
