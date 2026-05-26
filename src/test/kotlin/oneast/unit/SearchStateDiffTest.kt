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

    // -----------------------------------------------------------------
    // More interesting / less obvious behaviors
    // -----------------------------------------------------------------

    // ----- Variable bijection allows non-identity permutations -----
    @Test
    fun `variable swap is cost 0 because bijection allows it`() {
        // L0[V0, V1] vs L0[V1, V0]: the renaming {V0->V1, V1->V0} is a valid
        // bijection within the type, so cost 0.
        val s1 = state(mapOf(0 to 2), "foo" to NamedLabel(0, listOf(Variable(0), Variable(1))))
        val s2 = state(mapOf(0 to 2), "foo" to NamedLabel(0, listOf(Variable(1), Variable(0))))
        assertEquals(0, s1.diffTo(s2).cost)
    }

    @Test
    fun `repeated variable swap with consistent bijection is cost 0`() {
        // L0[V0, V1, V0, V1] vs L0[V5, V7, V5, V7] : V0->V5, V1->V7 is a valid bijection
        val s1 = state(
            mapOf(0 to 4),
            "foo" to NamedLabel(0, listOf(Variable(0), Variable(1), Variable(0), Variable(1)))
        )
        val s2 = state(
            mapOf(0 to 4),
            "foo" to NamedLabel(0, listOf(Variable(5), Variable(7), Variable(5), Variable(7)))
        )
        assertEquals(0, s1.diffTo(s2).cost)
    }

    @Test
    fun `variable bijection broken by inconsistent repetition`() {
        // L0[V0, V1, V0, V1] vs L0[V5, V7, V7, V5]: bind V0->V5, V1->V7, then
        // V0 vs V7 conflicts (cost 1), V1 vs V5 conflicts (cost 1). Total 2.
        val s1 = state(
            mapOf(0 to 4),
            "foo" to NamedLabel(0, listOf(Variable(0), Variable(1), Variable(0), Variable(1)))
        )
        val s2 = state(
            mapOf(0 to 4),
            "foo" to NamedLabel(0, listOf(Variable(5), Variable(7), Variable(7), Variable(5)))
        )
        assertEquals(2, s1.diffTo(s2).cost)
    }

    // ----- Cost is local to the mismatched subtrees; ratio reflects context -----
    @Test
    fun `mismatch cost depends only on mismatched subtree sizes, not depth - ratio shrinks with surrounding context`() {
        // Both cases have the SAME local mismatch: a Variable in expected vs
        // NamedLabel(0, [V0]) in actual. So in both, cost = size(V0) + size(L0[V0]) = 1 + 2 = 3.
        // The surrounding context (matching Arrows + Variables) is identical
        // between expected and actual at every position, so it adds 0 to cost.
        // Only the *ratio* (cost / expectedSize) shrinks as the surroundings grow.
        //
        //   deepExpected:  Arrow(V0, Arrow(V0, V0))            -- size 5
        //   deepActual:    Arrow(V0, Arrow(V0, L0[V0]))        -- size 6
        // The two Arrow spines align perfectly; only the deepest leaf disagrees.
        val deepExpected = state(
            mapOf(),
            "foo" to Arrow(Variable(0), Arrow(Variable(0), Variable(0)))
        )
        val deepActual = state(
            mapOf(0 to 1),
            "foo" to Arrow(
                Variable(0),
                Arrow(Variable(0), NamedLabel(0, listOf(Variable(0))))
            )
        )
        val deep = deepExpected.diffTo(deepActual)
        assertEquals(3, deep.cost)
        assertEquals(5, deep.expectedSize)
        assertEquals(3.0 / 5.0, deep.ratio)

        // Same V vs L0[V0] mismatch, now at the root with no surrounding context.
        val rootExpected = state(mapOf(), "foo" to Variable(0))
        val rootActual = state(mapOf(0 to 1), "foo" to NamedLabel(0, listOf(Variable(0))))
        val root = rootExpected.diffTo(rootActual)
        assertEquals(3, root.cost) // identical to deep case
        assertEquals(1, root.expectedSize)
        assertEquals(3.0, root.ratio) // but ratio is much worse
    }

    // ----- Arrow vs Label is strictly more costly than Var vs Label -----
    @Test
    fun `arrow vs label is strictly more costly than var vs label at same arity`() {
        // V0 (size 1) vs L0[V0, V0] (size 3) -> cost 4
        val varVsLabel = state(mapOf(), "foo" to Variable(0))
            .diffTo(state(mapOf(0 to 2), "foo" to NamedLabel(0, listOf(Variable(0), Variable(0)))))
        // Arrow(V0,V0) (size 3) vs L0[V0,V0] (size 3) -> cost 6
        val arrowVsLabel = state(mapOf(), "foo" to Arrow(Variable(0), Variable(0)))
            .diffTo(state(mapOf(0 to 2), "foo" to NamedLabel(0, listOf(Variable(0), Variable(0)))))
        assertTrue(arrowVsLabel.cost > varVsLabel.cost)
        assertEquals(4, varVsLabel.cost)
        assertEquals(6, arrowVsLabel.cost)
    }

    // ----- Cost upper bound -----
    @Test
    fun `cost is bounded by total node count of both sides`() {
        // Most extreme mismatch: completely different kinds at root.
        val s1 = state(
            mapOf(),
            "foo" to Arrow(Arrow(Variable(0), Variable(1)), Variable(0)) // size 5
        )
        val s2 = state(
            mapOf(0 to 1),
            "foo" to NamedLabel(0, listOf(Variable(0))) // size 2
        )
        val d = s1.diffTo(s2)
        assertTrue(d.cost <= s1.nodeCount() + s2.nodeCount())
        // root kind mismatch -> exactly sum
        assertEquals(7, d.cost)
    }

    // ----- All holes expected -----
    @Test
    fun `all-holes expected vs fully-specified actual costs full actual size`() {
        // expected: Arrow(hole, Arrow(hole, hole)) -- size 5, all interior nodes are holes
        // actual:   Arrow(L0[V0], Arrow(V0, L0[V0])) -- size 7
        // Arrows match (3 of them: roots + 1 inner). Holes vs subtrees:
        //   pos 1: hole vs L0[V0] (size 2) -> 2
        //   pos 2: hole vs V0 (size 1) -> 1
        //   pos 3: hole vs L0[V0] (size 2) -> 2
        // Total: 5.
        val s1 = state(
            mapOf(),
            "foo" to Arrow(TypeHole(), Arrow(TypeHole(), TypeHole()))
        )
        val s2 = state(
            mapOf(0 to 1),
            "foo" to Arrow(
                NamedLabel(0, listOf(Variable(0))),
                Arrow(Variable(0), NamedLabel(0, listOf(Variable(0))))
            )
        )
        assertEquals(5, s1.diffTo(s2).cost)
    }

    // ----- Disjoint name sets -----
    @Test
    fun `disjoint name sets give cost equal to sum of all sizes`() {
        val s1 = state(
            mapOf(0 to 2),
            "foo" to NamedLabel(0, listOf(Variable(0), Variable(0))) // size 3
        )
        val s2 = state(
            mapOf(),
            "bar" to Arrow(Variable(0), Variable(1)) // size 3
        )
        val d = s1.diffTo(s2)
        assertEquals(6, d.cost)
        assertEquals(3, d.expectedSize)
        assertEquals(2.0, d.ratio)
    }

    // ----- Cost is symmetric but ratio is not -----
    @Test
    fun `cost is symmetric but ratio is not when sizes differ`() {
        // expected: L0[V0, V0, V0, V0] size 5; actual: V0 size 1
        val big = state(
            mapOf(0 to 4),
            "foo" to NamedLabel(0, listOf(Variable(0), Variable(0), Variable(0), Variable(0)))
        )
        val small = state(mapOf(), "foo" to Variable(0))
        val d1 = big.diffTo(small) // 5 + 1 = 6 cost, expectedSize 5
        val d2 = small.diffTo(big) // 6 cost, expectedSize 1
        assertEquals(d1.cost, d2.cost)
        assertEquals(6, d1.cost)
        assertEquals(6.0 / 5.0, d1.ratio)
        assertEquals(6.0, d2.ratio)
    }

    // ----- Cascading label conflict -----
    @Test
    fun `same label appearing in many positions all charge after first binding`() {
        // expected: L0[L0[L0]]  -- L0 appears at 3 positions
        // actual:   L0[L5[L9]]  -- first L0 binds 0->0, then L0 vs L5 fails (cost 1),
        //                           L0 vs L9 fails (cost 1) because mapRev would conflict
        // wait, let me trace:
        // outer L0 vs L0: bind 0->0. cost 0.
        // middle L0 vs L5: map[0]=0 != 5. cost 1. (no map mutation on failure)
        // inner L0 vs L9: map[0]=0 != 9. cost 1.
        // total: 2.
        val s1 = state(
            mapOf(0 to 1),
            "foo" to NamedLabel(0, listOf(NamedLabel(0, listOf(NamedLabel(0, listOf())))))
        )
        val s2 = state(
            mapOf(0 to 1, 5 to 1, 9 to 0),
            "foo" to NamedLabel(0, listOf(NamedLabel(5, listOf(NamedLabel(9, listOf())))))
        )
        assertEquals(2, s1.diffTo(s2).cost)
    }

    // ----- Name iteration order shouldn't affect cost when there are no
    // ----- cross-name label conflicts -----
    @Test
    fun `cost independent of name insertion order when no cross-name label conflicts`() {
        // Two states differ only by names map insertion order; each name uses
        // disjoint labels so binding order can't matter.
        val labels1 = listOf(
            "a" to NamedLabel(0, listOf(Variable(0))),
            "b" to NamedLabel(1, listOf(Variable(0), Variable(1)))
        )
        val labels2 = listOf(
            "a" to NamedLabel(5, listOf(Variable(7))),
            "b" to NamedLabel(8, listOf(Variable(3), Variable(4)))
        )
        val s1Forward = SearchState(
            names = labels1.withIndex().associate { it.value.first to it.index },
            types = labels1.map { it.second },
            labelArities = mapOf(0 to 1, 1 to 2)
        )
        val s1Reversed = SearchState(
            names = labels1.reversed().withIndex().associate { it.value.first to it.index },
            types = labels1.reversed().map { it.second },
            labelArities = mapOf(0 to 1, 1 to 2)
        )
        val s2 = SearchState(
            names = labels2.withIndex().associate { it.value.first to it.index },
            types = labels2.map { it.second },
            labelArities = mapOf(5 to 1, 8 to 2)
        )
        assertEquals(s1Forward.diffTo(s2).cost, s1Reversed.diffTo(s2).cost)
        assertEquals(0, s1Forward.diffTo(s2).cost)
    }

    // ----- Variable in expected vs hole in actual is cost 1 (size of variable) -----
    @Test
    fun `variable expected vs hole actual costs 1`() {
        val s1 = state(mapOf(), "foo" to Variable(0))
        val s2 = state(mapOf(), "foo" to TypeHole())
        assertEquals(1, s1.diffTo(s2).cost)
    }

    // ----- Label arity 0 in expected vs hole in actual is cost 1 -----
    @Test
    fun `arity-0 label expected vs hole actual costs 1`() {
        val s1 = state(mapOf(0 to 0), "foo" to NamedLabel(0, listOf()))
        val s2 = state(mapOf(), "foo" to TypeHole())
        assertEquals(1, s1.diffTo(s2).cost)
    }

    // ----- Realistic medium-size example -----
    @Test
    fun `medium realistic example combining structural and naming features`() {
        // expected: typical functional-style components
        //   id:   'a -> 'a
        //   pair: 'a -> 'b -> Pair['a, 'b]   (L0 has arity 2)
        //   fst:  Pair['a, 'b] -> 'a
        val s1 = state(
            mapOf(0 to 2),
            "id" to Arrow(Variable(0), Variable(0)),
            "pair" to Arrow(
                Variable(0),
                Arrow(Variable(1), NamedLabel(0, listOf(Variable(0), Variable(1))))
            ),
            "fst" to Arrow(NamedLabel(0, listOf(Variable(0), Variable(1))), Variable(0))
        )
        // actual: same up to renaming (L0 -> L9; vars renamed per type)
        val s2 = state(
            mapOf(9 to 2),
            "id" to Arrow(Variable(3), Variable(3)),
            "pair" to Arrow(
                Variable(7),
                Arrow(Variable(8), NamedLabel(9, listOf(Variable(7), Variable(8))))
            ),
            "fst" to Arrow(NamedLabel(9, listOf(Variable(11), Variable(22))), Variable(11))
        )
        val d = s1.diffTo(s2)
        assertEquals(0, d.cost)
        assertTrue(s1.equivalentTo(s2))
    }

    @Test
    fun `medium realistic example with one small mistake gives small cost`() {
        // Same as above but `fst` returns 'b instead of 'a (swap output variable).
        val s1 = state(
            mapOf(0 to 2),
            "id" to Arrow(Variable(0), Variable(0)),
            "pair" to Arrow(
                Variable(0),
                Arrow(Variable(1), NamedLabel(0, listOf(Variable(0), Variable(1))))
            ),
            "fst" to Arrow(NamedLabel(0, listOf(Variable(0), Variable(1))), Variable(0))
        )
        val s2 = state(
            mapOf(0 to 2),
            "id" to Arrow(Variable(0), Variable(0)),
            "pair" to Arrow(
                Variable(0),
                Arrow(Variable(1), NamedLabel(0, listOf(Variable(0), Variable(1))))
            ),
            "fst" to Arrow(NamedLabel(0, listOf(Variable(0), Variable(1))), Variable(1)) // bug
        )
        val d = s1.diffTo(s2)
        // Only `fst`'s output var differs from the bijection -> cost 1
        assertEquals(1, d.cost)
        // expectedSize: id (3) + pair (3 + 4 = 7) + fst (5) = 15
        assertEquals(15, d.expectedSize)
    }

    @Test
    fun `medium realistic example with arrow-vs-label confusion is large cost`() {
        // Same baseline but `fst` is mis-typed as Pair[..] -> Pair[..] (an Arrow
        // node at the root replaced with... wait, it already is an Arrow. Let's
        // instead replace the *input* of fst with an Arrow type by mistake.
        val s1 = state(
            mapOf(0 to 2),
            "fst" to Arrow(NamedLabel(0, listOf(Variable(0), Variable(1))), Variable(0))
        )
        val s2 = state(
            mapOf(),
            // mis-typed: input is Arrow(V0, V1) instead of Pair[V0, V1]
            "fst" to Arrow(Arrow(Variable(0), Variable(1)), Variable(0))
        )
        val d = s1.diffTo(s2)
        // L0[V0, V1] (size 3) vs Arrow(V0, V1) (size 3) at fst's left -> cost 6
        // rest matches -> total 6.
        assertEquals(6, d.cost)
    }

    // ----- "Negative" property: subtree-size cost in two name-trees combine
    // ----- additively, no implicit discount -----
    @Test
    fun `independent subtree-size costs add across names`() {
        val s1 = state(
            mapOf(),
            "a" to Variable(0),
            "b" to Variable(0)
        )
        val s2 = state(
            mapOf(0 to 2),
            "a" to NamedLabel(0, listOf(Variable(0), Variable(0))), // size 3
            "b" to NamedLabel(0, listOf(Variable(0), Variable(0)))  // size 3
        )
        // a: V vs L0[..] -> 1 + 3 = 4. b: V vs L0[..] -> 1 + 3 = 4. Total 8.
        assertEquals(8, s1.diffTo(s2).cost)
    }

    // ----- Hole anywhere in either side: cost equals size of the OTHER side -----
    @Test
    fun `hole on either side costs size of the non-hole regardless of position`() {
        // Asymmetry safeguard: confirms that t1=hole vs t2=L0[V0] and
        // t1=L0[V0] vs t2=hole give the same cost.
        val hole = state(mapOf(), "foo" to TypeHole())
        val tree = state(mapOf(0 to 1), "foo" to NamedLabel(0, listOf(Variable(0))))
        assertEquals(hole.diffTo(tree).cost, tree.diffTo(hole).cost)
        assertEquals(2, hole.diffTo(tree).cost)
    }
}
