package oneast.unit

import oneast.*
import org.junit.jupiter.api.Test
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
}
