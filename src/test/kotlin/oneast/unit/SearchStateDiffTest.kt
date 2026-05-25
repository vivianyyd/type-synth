package oneast.unit

import oneast.*
import org.junit.jupiter.api.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class SearchStateDiffTest {

    private fun state(
        labelArities: Map<Int, Int>,
        vararg entries: Pair<String, Type>
    ): SearchState {
        val (names, types) = entries.toList().unzip()
        return SearchState(
            names = names.withIndex().associate { it.value to it.index },
            types = types,
            labelArities = labelArities
        )
    }

    // ----- nodeCount -----
    @Test
    fun `nodeCount Variable is 1`() {
        assertEquals(1, Variable(0).nodeCount())
    }

    @Test
    fun `nodeCount TypeHole is 1`() {
        assertEquals(1, TypeHole().nodeCount())
    }

    @Test
    fun `nodeCount Blank is 1`() {
        assertEquals(1, Blank(labelOnly = true).nodeCount())
    }

    @Test
    fun `nodeCount NamedLabel arity 0 is 1`() {
        assertEquals(1, NamedLabel(0, listOf()).nodeCount())
    }

    @Test
    fun `nodeCount L0 of V V is 3`() {
        assertEquals(3, NamedLabel(0, listOf(Variable(0), Variable(0))).nodeCount())
    }

    @Test
    fun `nodeCount Arrow of V V is 3`() {
        assertEquals(3, Arrow(Variable(0), Variable(1)).nodeCount())
    }

    @Test
    fun `nodeCount nested arrow is 5`() {
        // (V0 -> V1) -> V0
        assertEquals(5, Arrow(Arrow(Variable(0), Variable(1)), Variable(0)).nodeCount())
    }

    @Test
    fun `nodeCount of state sums type nodes`() {
        val s = state(
            mapOf(0 to 2),
            "foo" to NamedLabel(0, listOf(Variable(0), Variable(1))),
            "bar" to Variable(0)
        )
        assertEquals(4, s.nodeCount())
    }

    // ----- Diff is 0 for equivalent states -----
    @Test
    fun `identical states have diff 0`() {
        val s = state(
            mapOf(0 to 2),
            "foo" to NamedLabel(0, listOf(Variable(0), Variable(1)))
        )
        val d = s.diffTo(s)
        assertEquals(0, d.cost)
        assertEquals(s.nodeCount(), d.expectedSize)
        assertEquals(0.0, d.ratio)
    }

    @Test
    fun `equivalent states with renaming have diff 0 - user example`() {
        val s1 = state(
            mapOf(0 to 1, 1 to 3),
            "foo" to NamedLabel(0, listOf(Variable(0))),
            "bar" to NamedLabel(
                1,
                listOf(
                    NamedLabel(0, listOf(Variable(0))),
                    Variable(0),
                    Variable(1)
                )
            )
        )
        val s2 = state(
            mapOf(7 to 1, 5 to 3),
            "foo" to NamedLabel(7, listOf(Variable(4))),
            "bar" to NamedLabel(
                5,
                listOf(
                    NamedLabel(7, listOf(Variable(6))),
                    Variable(6),
                    Variable(8)
                )
            )
        )
        assertTrue(s1.equivalentTo(s2))
        assertEquals(0, s1.diffTo(s2).cost)
        assertEquals(0, s2.diffTo(s1).cost)
    }

    @Test
    fun `empty states have diff 0`() {
        val d = SearchState.emptyState.diffTo(SearchState.emptyState)
        assertEquals(0, d.cost)
        assertEquals(0, d.expectedSize)
    }

    // ----- Single node mismatches -----
    @Test
    fun `single variable bijection conflict costs 1`() {
        // L0[V0, V1] vs L0[V0, V0] : second var V1 must map to something other than V0 (taken),
        // bijection fails -> cost 1
        val s1 = state(
            mapOf(0 to 2),
            "foo" to NamedLabel(0, listOf(Variable(0), Variable(1)))
        )
        val s2 = state(
            mapOf(0 to 2),
            "foo" to NamedLabel(0, listOf(Variable(0), Variable(0)))
        )
        assertEquals(1, s1.diffTo(s2).cost)
    }

    @Test
    fun `single label bijection conflict same arity costs 1 and recurses`() {
        // L0[L0] vs L5[L9]: bind 0->5, then L0 vs L9 conflicts -> cost 1
        val s1 = state(
            mapOf(0 to 1),
            "foo" to NamedLabel(0, listOf(NamedLabel(0, listOf())))
        )
        val s2 = state(
            mapOf(5 to 1, 9 to 0),
            "foo" to NamedLabel(5, listOf(NamedLabel(9, listOf())))
        )
        assertEquals(1, s1.diffTo(s2).cost)
    }

    @Test
    fun `label arity mismatch costs sum of sizes`() {
        // L0[V0] (size 2) vs L0[V0, V0] (size 3) -> cost 5
        val s1 = state(mapOf(0 to 1), "foo" to NamedLabel(0, listOf(Variable(0))))
        val s2 = state(mapOf(0 to 2), "foo" to NamedLabel(0, listOf(Variable(0), Variable(0))))
        assertEquals(5, s1.diffTo(s2).cost)
    }

    // ----- Kind mismatches -----
    @Test
    fun `arrow vs label costs sum of sizes`() {
        // Arrow(V0,V1) (size 3) vs L0[V0,V1] arity 2 (size 3) -> cost 6
        val s1 = state(mapOf(), "foo" to Arrow(Variable(0), Variable(1)))
        val s2 = state(mapOf(0 to 2), "foo" to NamedLabel(0, listOf(Variable(0), Variable(1))))
        assertEquals(6, s1.diffTo(s2).cost)
    }

    @Test
    fun `variable vs label arity 0 costs 2`() {
        // V0 (size 1) vs L0 (size 1) -> cost 2
        val s1 = state(mapOf(), "foo" to Variable(0))
        val s2 = state(mapOf(0 to 0), "foo" to NamedLabel(0, listOf()))
        assertEquals(2, s1.diffTo(s2).cost)
    }

    @Test
    fun `variable vs arrow costs sum of sizes`() {
        // V0 vs Arrow(V0, V0) -> 1 + 3 = 4
        val s1 = state(mapOf(), "foo" to Variable(0))
        val s2 = state(mapOf(), "foo" to Arrow(Variable(0), Variable(0)))
        assertEquals(4, s1.diffTo(s2).cost)
    }

    @Test
    fun `variable vs deep label tree`() {
        // V0 (size 1) vs L0[V0, V0] (size 3) -> 4
        val s1 = state(mapOf(), "foo" to Variable(0))
        val s2 = state(mapOf(0 to 2), "foo" to NamedLabel(0, listOf(Variable(0), Variable(0))))
        assertEquals(4, s1.diffTo(s2).cost)
    }

    // ----- Holes -----
    @Test
    fun `TypeHole vs TypeHole costs 0`() {
        val s1 = state(mapOf(), "foo" to TypeHole())
        val s2 = state(mapOf(), "foo" to TypeHole())
        assertEquals(0, s1.diffTo(s2).cost)
    }

    @Test
    fun `TypeHole vs Blank costs 0`() {
        val s1 = state(mapOf(), "foo" to TypeHole())
        val s2 = state(mapOf(), "foo" to Blank(labelOnly = true))
        assertEquals(0, s1.diffTo(s2).cost)
    }

    @Test
    fun `expected hole vs actual non-hole costs size of non-hole`() {
        // TypeHole vs L0[V0, V0] (size 3) -> cost 3
        val s1 = state(mapOf(), "foo" to TypeHole())
        val s2 = state(mapOf(0 to 2), "foo" to NamedLabel(0, listOf(Variable(0), Variable(0))))
        assertEquals(3, s1.diffTo(s2).cost)
    }

    @Test
    fun `expected non-hole vs actual hole costs size of non-hole`() {
        val s1 = state(mapOf(0 to 2), "foo" to NamedLabel(0, listOf(Variable(0), Variable(0))))
        val s2 = state(mapOf(), "foo" to TypeHole())
        assertEquals(3, s1.diffTo(s2).cost)
    }

    @Test
    fun `nested hole vs nested non-hole charges size of non-hole subtree`() {
        // L0[TypeHole] vs L0[L1[V0, V0]] -> L0 matches, hole vs L1[V0,V0] (size 3) -> cost 3
        val s1 = state(mapOf(0 to 1), "foo" to NamedLabel(0, listOf(TypeHole())))
        val s2 = state(
            mapOf(0 to 1, 1 to 2),
            "foo" to NamedLabel(0, listOf(NamedLabel(1, listOf(Variable(0), Variable(0)))))
        )
        assertEquals(3, s1.diffTo(s2).cost)
    }

    // ----- Names appearing on only one side -----
    @Test
    fun `name only in expected adds size of expected tree`() {
        val s1 = state(
            mapOf(0 to 2),
            "foo" to NamedLabel(0, listOf(Variable(0), Variable(0))), // size 3
            "bar" to Variable(0) // size 1
        )
        val s2 = state(
            mapOf(0 to 2),
            "foo" to NamedLabel(0, listOf(Variable(0), Variable(0)))
        )
        // foo matches (cost 0), bar missing in actual -> +1
        val d = s1.diffTo(s2)
        assertEquals(1, d.cost)
        assertEquals(4, d.expectedSize)
    }

    @Test
    fun `name only in actual adds size of actual tree`() {
        val s1 = state(
            mapOf(0 to 2),
            "foo" to NamedLabel(0, listOf(Variable(0), Variable(0)))
        )
        val s2 = state(
            mapOf(0 to 2),
            "foo" to NamedLabel(0, listOf(Variable(0), Variable(0))),
            "bar" to Arrow(Variable(0), Variable(1)) // size 3
        )
        val d = s1.diffTo(s2)
        assertEquals(3, d.cost)
        assertEquals(3, d.expectedSize)
    }

    // ----- Ratio -----
    @Test
    fun `ratio is cost over expected size`() {
        // expected size 3, one var bijection conflict -> cost 1, ratio 1/3
        val s1 = state(
            mapOf(0 to 2),
            "foo" to NamedLabel(0, listOf(Variable(0), Variable(1)))
        )
        val s2 = state(
            mapOf(0 to 2),
            "foo" to NamedLabel(0, listOf(Variable(0), Variable(0)))
        )
        val d = s1.diffTo(s2)
        assertEquals(3, d.expectedSize)
        assertEquals(1, d.cost)
        assertEquals(1.0 / 3.0, d.ratio)
    }

    @Test
    fun `ratio of zero cost is 0`() {
        val s = state(mapOf(0 to 0), "foo" to NamedLabel(0, listOf()))
        assertEquals(0.0, s.diffTo(s).ratio)
    }

    @Test
    fun `ratio of empty expected with 0 cost is 0`() {
        assertEquals(0.0, SearchState.emptyState.diffTo(SearchState.emptyState).ratio)
    }

    @Test
    fun `ratio of empty expected with positive cost is infinity`() {
        val s2 = state(mapOf(0 to 0), "foo" to NamedLabel(0, listOf()))
        assertEquals(Double.POSITIVE_INFINITY, SearchState.emptyState.diffTo(s2).ratio)
    }

    @Test
    fun `ratio can exceed 1`() {
        // expected = hole (size 1), actual = big tree (size 3) -> cost 3, ratio 3
        val s1 = state(mapOf(), "foo" to TypeHole())
        val s2 = state(mapOf(0 to 2), "foo" to NamedLabel(0, listOf(Variable(0), Variable(0))))
        val d = s1.diffTo(s2)
        assertEquals(3, d.cost)
        assertEquals(1, d.expectedSize)
        assertEquals(3.0, d.ratio)
    }

    // ----- Global label binding across names -----
    @Test
    fun `consistent global label binding across names cost 0`() {
        val s1 = state(
            mapOf(0 to 0, 1 to 0),
            "a" to NamedLabel(0, listOf()),
            "b" to NamedLabel(1, listOf())
        )
        val s2 = state(
            mapOf(5 to 0, 9 to 0),
            "a" to NamedLabel(5, listOf()),
            "b" to NamedLabel(9, listOf())
        )
        assertEquals(0, s1.diffTo(s2).cost)
    }

    @Test
    fun `inconsistent global label binding across names costs 1`() {
        // s1 uses L0 in both names; s2 uses L5, L9.
        // First name binds 0->5; second name's L0 vs L9 conflicts -> cost 1.
        val s1 = state(
            mapOf(0 to 0),
            "a" to NamedLabel(0, listOf()),
            "b" to NamedLabel(0, listOf())
        )
        val s2 = state(
            mapOf(5 to 0, 9 to 0),
            "a" to NamedLabel(5, listOf()),
            "b" to NamedLabel(9, listOf())
        )
        assertEquals(1, s1.diffTo(s2).cost)
    }

    @Test
    fun `local variable binding does not cross names`() {
        // Same V0 in two types of expected; actual uses different vars per type.
        // Each name gets fresh varMap, so cost 0.
        val s1 = state(
            mapOf(0 to 1),
            "a" to NamedLabel(0, listOf(Variable(0))),
            "b" to NamedLabel(0, listOf(Variable(0)))
        )
        val s2 = state(
            mapOf(0 to 1),
            "a" to NamedLabel(0, listOf(Variable(4))),
            "b" to NamedLabel(0, listOf(Variable(99)))
        )
        assertEquals(0, s1.diffTo(s2).cost)
    }

    // ----- Nested mismatch -----
    @Test
    fun `nested mismatch only counts local cost`() {
        // Arrow(L0[V0], V1) vs Arrow(L0[V0], V0):
        // arrows match (0), L0[V0] vs L0[V0] match (0), V1 vs V0 conflict (V0 mapped to V0 from left) -> 1
        val s1 = state(
            mapOf(0 to 1),
            "foo" to Arrow(NamedLabel(0, listOf(Variable(0))), Variable(1))
        )
        val s2 = state(
            mapOf(0 to 1),
            "foo" to Arrow(NamedLabel(0, listOf(Variable(0))), Variable(0))
        )
        assertEquals(1, s1.diffTo(s2).cost)
    }

    @Test
    fun `deeply nested kind mismatch costs subtree sum`() {
        // L0[L0[V0]] vs L0[Arrow(V0, V0)]
        // Outer L0 matches. Inner: L0[V0] (size 2) vs Arrow(V0,V0) (size 3) kind mismatch -> 5
        val s1 = state(
            mapOf(0 to 1),
            "foo" to NamedLabel(0, listOf(NamedLabel(0, listOf(Variable(0)))))
        )
        val s2 = state(
            mapOf(0 to 1),
            "foo" to NamedLabel(0, listOf(Arrow(Variable(0), Variable(0))))
        )
        assertEquals(5, s1.diffTo(s2).cost)
    }

    // ----- Multiple costs combined -----
    @Test
    fun `multiple independent mismatches sum`() {
        // foo: cost 1 (var conflict). bar: cost 2 (V vs L0 arity 0).
        val s1 = state(
            mapOf(0 to 2),
            "foo" to NamedLabel(0, listOf(Variable(0), Variable(1))),
            "bar" to Variable(0)
        )
        val s2 = state(
            mapOf(0 to 2, 5 to 0),
            "foo" to NamedLabel(0, listOf(Variable(0), Variable(0))),
            "bar" to NamedLabel(5, listOf())
        )
        assertEquals(3, s1.diffTo(s2).cost)
    }

    // ----- Equivalence cross-check -----
    @Test
    fun `equivalent implies cost 0`() {
        val s1 = state(
            mapOf(0 to 1, 1 to 3),
            "foo" to NamedLabel(0, listOf(Variable(0))),
            "bar" to NamedLabel(
                1,
                listOf(
                    NamedLabel(0, listOf(Variable(0))),
                    Variable(0),
                    Variable(1)
                )
            )
        )
        val s2 = state(
            mapOf(7 to 1, 5 to 3),
            "foo" to NamedLabel(7, listOf(Variable(4))),
            "bar" to NamedLabel(
                5,
                listOf(
                    NamedLabel(7, listOf(Variable(6))),
                    Variable(6),
                    Variable(8)
                )
            )
        )
        assertTrue(s1.equivalentTo(s2))
        assertEquals(0, s1.diffTo(s2).cost)
    }

    @Test
    fun `non-equivalent implies cost greater than 0`() {
        val s1 = state(mapOf(0 to 0), "foo" to NamedLabel(0, listOf()))
        val s2 = state(mapOf(), "foo" to Variable(0))
        assertTrue(s1.diffTo(s2).cost > 0)
    }

    // ----- Cost symmetry -----
    @Test
    fun `cost is symmetric across simple example`() {
        val s1 = state(
            mapOf(0 to 2),
            "foo" to NamedLabel(0, listOf(Variable(0), Variable(1)))
        )
        val s2 = state(
            mapOf(0 to 2),
            "foo" to NamedLabel(0, listOf(Variable(0), Variable(0)))
        )
        assertEquals(s1.diffTo(s2).cost, s2.diffTo(s1).cost)
    }

    @Test
    fun `cost is symmetric for kind mismatch`() {
        val s1 = state(mapOf(), "foo" to Arrow(Variable(0), Variable(1)))
        val s2 = state(mapOf(0 to 2), "foo" to NamedLabel(0, listOf(Variable(0), Variable(1))))
        assertEquals(s1.diffTo(s2).cost, s2.diffTo(s1).cost)
    }

    @Test
    fun `cost is symmetric for global label conflict`() {
        val s1 = state(
            mapOf(0 to 0),
            "a" to NamedLabel(0, listOf()),
            "b" to NamedLabel(0, listOf())
        )
        val s2 = state(
            mapOf(5 to 0, 9 to 0),
            "a" to NamedLabel(5, listOf()),
            "b" to NamedLabel(9, listOf())
        )
        assertEquals(s1.diffTo(s2).cost, s2.diffTo(s1).cost)
    }

    // ----- StateDiff data class equality -----
    @Test
    fun `StateDiff has expected fields`() {
        val d = StateDiff(cost = 5, expectedSize = 10)
        assertEquals(5, d.cost)
        assertEquals(10, d.expectedSize)
        assertEquals(0.5, d.ratio)
    }
}
