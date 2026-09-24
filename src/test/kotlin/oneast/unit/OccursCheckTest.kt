package oneast.unit

import oneast.*
import org.junit.jupiter.api.Test
import query.App
import query.Name
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
    private val a = Variable(0)
    private val I = NamedLabel(0, listOf())
    private val labelArities = mapOf(0 to 0, 1 to 0, 2 to 1, 3 to 2)

    /** Label 2 has arity 1; label 3 has arity 2. */
    private fun l(t: Type) = NamedLabel(2, listOf(t))

    private fun pair(x: Type, y: Type) = NamedLabel(3, listOf(x, y))

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

    @Test
    fun `type unified with its own proper subterm`() {
        for (depth in 2..6) {
            var deep: Type = a
            repeat(depth) { deep = l(deep) }
            for (swap in listOf(false, true)) {
                // f's argument pairs L^depth[a] with L[a], sharing one variable; g's pairs one
                // type with itself, so the two must be equal — which needs an infinite type.
                val param = if (swap) pair(l(a), deep) else pair(deep, l(a))
                val context = SearchState(
                    names = mapOf("f" to 0, "g" to 1),
                    types = listOf(Arrow(param, I), pair(a, a)),
                    labelArities = labelArities
                )
                val unification = OneUnification(context, listOf(App(Name("f"), Name("g"))))
                assertFalse(unification.ok, "depth=$depth swap=$swap")
            }
        }
    }
}
