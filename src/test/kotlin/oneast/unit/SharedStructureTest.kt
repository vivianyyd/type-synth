package oneast.unit

import oneast.TypeGraph
import org.junit.jupiter.api.Test
import kotlin.test.assertEquals

/** Two constructor nodes built from the same label and the same argument nodes. */
class SharedStructureTest {
    private val L = 3

    @Test
    fun `two copies of L(a, b) denote the same type`() {
        val graph = TypeGraph()
        val a = graph.rigid(0, 0)
        val b = graph.rigid(1, 0)
        val first = graph.ctor(L, intArrayOf(a, b))
        val second = graph.ctor(L, intArrayOf(a, b))
        assertEquals(graph.typeAt(first), graph.typeAt(second))

        // Still the same after unifying only one of them with something.
        val c = graph.rigid(2, 0)
        val d = graph.rigid(3, 0)
        assertEquals(true, graph.merge(first, graph.ctor(L, intArrayOf(c, d))))
        assertEquals(graph.typeAt(first), graph.typeAt(second))
    }

    @Test
    fun `x and y merged with the same L(a@1, b@1) node share a class`() {
        val graph = TypeGraph()
        val node = graph.ctor(L, intArrayOf(graph.rigid(0, 1), graph.rigid(1, 1)))
        val x = graph.freshVar()
        val y = graph.freshVar()
        graph.merge(x, node)
        graph.merge(y, node)
        assertEquals(graph.find(x), graph.find(y))
    }
}
