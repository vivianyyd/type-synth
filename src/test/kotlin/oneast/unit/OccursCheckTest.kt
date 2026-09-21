package oneast.unit

import oneast.*
import org.junit.jupiter.api.Test
import kotlin.test.assertFalse
import kotlin.test.assertTrue

/**
 * Unification must reject constraints only an infinite type could satisfy.
 *
 * In a substitution-based unifier, structure enters the problem only when a variable is bound, so
 * one occurs check at each binding is complete. In a union-find, structure also enters when two
 * classes that both already carry a constructor are merged, so the check belongs at every merge.
 */
class OccursCheckTest {
    /** Unifying L[L[w]] with L[w] asks for the infinite type L[L[L[...]]]. */
    @Test
    fun `graph rejects a term unified with its own subterm`() {
        for (outerFirst in listOf(true, false)) {
            // Pad one side's class so that union by size picks each half in turn as the one whose
            // constructor survives the merge: only one of them is the half that must not occur.
            for (padding in 0..3) {
                val graph = TypeGraph()
                val w = graph.freshVar()
                val inner = graph.ctor(2, intArrayOf(w))
                val outer = graph.ctor(2, intArrayOf(inner))
                repeat(padding) { graph.merge(outer, graph.freshVar()) }
                val merged =
                    if (outerFirst) graph.merge(outer, inner) else graph.merge(inner, outer)
                assertFalse(merged, "outerFirst=$outerFirst padding=$padding")
                assertTrue(graph.acyclic(), "outerFirst=$outerFirst padding=$padding")
            }
        }
    }
}
