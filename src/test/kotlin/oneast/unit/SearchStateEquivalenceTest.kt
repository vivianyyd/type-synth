package oneast.unit

import oneast.Arrow
import oneast.Blank
import oneast.NamedLabel
import oneast.SearchState
import oneast.Type
import oneast.TypeHole
import oneast.Variable
import oneast.equivalentTo
import org.junit.jupiter.api.Test
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class SearchStateEquivalenceTest {

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

    // ----- User's example -----
    @Test
    fun `user provided example - label and var renaming combined`() {
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
        assertTrue(s2.equivalentTo(s1))
    }

    @Test
    fun `inj`() {
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
                    Variable(6)
                )
            )
        )
        assertFalse(s1.equivalentTo(s2))
        assertFalse(s2.equivalentTo(s1))
    }

    // ----- Trivial / reflexivity -----
    @Test
    fun `empty states are equivalent`() {
        assertTrue(SearchState.emptyState.equivalentTo(SearchState.emptyState))
    }

    @Test
    fun `reflexivity - state is equivalent to itself`() {
        val s = state(
            mapOf(0 to 2),
            "foo" to NamedLabel(0, listOf(Variable(0), Variable(1)))
        )
        assertTrue(s.equivalentTo(s))
    }

    // ----- Name keys -----
    @Test
    fun `different name keys are not equivalent`() {
        val s1 = state(mapOf(0 to 0), "foo" to NamedLabel(0, listOf()))
        val s2 = state(mapOf(0 to 0), "bar" to NamedLabel(0, listOf()))
        assertFalse(s1.equivalentTo(s2))
    }

    @Test
    fun `different number of names not equivalent`() {
        val s1 = state(
            mapOf(0 to 0),
            "foo" to NamedLabel(0, listOf()),
            "bar" to NamedLabel(0, listOf())
        )
        val s2 = state(mapOf(0 to 0), "foo" to NamedLabel(0, listOf()))
        assertFalse(s1.equivalentTo(s2))
    }

    // ----- Variable renaming -----
    @Test
    fun `simple variable renaming within one type`() {
        val s1 = state(
            mapOf(),
            "foo" to Arrow(Variable(0), Variable(1))
        )
        val s2 = state(
            mapOf(),
            "foo" to Arrow(Variable(7), Variable(9))
        )
        assertTrue(s1.equivalentTo(s2))
    }

    @Test
    fun `variable renaming must be bijective - one var maps to two`() {
        // V0 -> V5 first, then V0 again must map to V5 (not V6)
        val s1 = state(
            mapOf(0 to 2),
            "foo" to NamedLabel(0, listOf(Variable(0), Variable(0)))
        )
        val s2 = state(
            mapOf(0 to 2),
            "foo" to NamedLabel(0, listOf(Variable(5), Variable(6)))
        )
        assertFalse(s1.equivalentTo(s2))
    }

    @Test
    fun `variable renaming must be bijective - two vars map to one`() {
        val s1 = state(
            mapOf(0 to 2),
            "foo" to NamedLabel(0, listOf(Variable(0), Variable(1)))
        )
        val s2 = state(
            mapOf(0 to 2),
            "foo" to NamedLabel(0, listOf(Variable(5), Variable(5)))
        )
        assertFalse(s1.equivalentTo(s2))
    }

    @Test
    fun `variable repetition preserved - both sides identical structure`() {
        val s1 = state(
            mapOf(0 to 2),
            "foo" to NamedLabel(0, listOf(Variable(0), Variable(0)))
        )
        val s2 = state(
            mapOf(0 to 2),
            "foo" to NamedLabel(0, listOf(Variable(9), Variable(9)))
        )
        assertTrue(s1.equivalentTo(s2))
    }

    @Test
    fun `variable renaming is local per type - same var name maps differently`() {
        // In s1 both types use V0; mapping is different per type in s2.
        val s1 = state(
            mapOf(0 to 1),
            "foo" to NamedLabel(0, listOf(Variable(0))),
            "bar" to NamedLabel(0, listOf(Variable(0)))
        )
        val s2 = state(
            mapOf(0 to 1),
            "foo" to NamedLabel(0, listOf(Variable(4))),
            "bar" to NamedLabel(0, listOf(Variable(99)))
        )
        assertTrue(s1.equivalentTo(s2))
    }

    // ----- Label renaming -----
    @Test
    fun `label renaming consistent across types`() {
        val s1 = state(
            mapOf(0 to 0, 1 to 0),
            "foo" to NamedLabel(0, listOf()),
            "bar" to NamedLabel(1, listOf())
        )
        val s2 = state(
            mapOf(2 to 0, 3 to 0),
            "foo" to NamedLabel(2, listOf()),
            "bar" to NamedLabel(3, listOf())
        )
        assertTrue(s1.equivalentTo(s2))
    }

    @Test
    fun `label renaming inconsistent across types - not equivalent`() {
        // s1 uses L0 in both, s2 uses L2 in foo but L3 in bar.
        val s1 = state(
            mapOf(0 to 0),
            "foo" to NamedLabel(0, listOf()),
            "bar" to NamedLabel(0, listOf())
        )
        val s2 = state(
            mapOf(2 to 0, 3 to 0),
            "foo" to NamedLabel(2, listOf()),
            "bar" to NamedLabel(3, listOf())
        )
        assertFalse(s1.equivalentTo(s2))
    }

    @Test
    fun `label bijection - two labels mapped to one - not equivalent`() {
        val s1 = state(
            mapOf(0 to 0, 1 to 0),
            "foo" to NamedLabel(0, listOf()),
            "bar" to NamedLabel(1, listOf())
        )
        val s2 = state(
            mapOf(7 to 0),
            "foo" to NamedLabel(7, listOf()),
            "bar" to NamedLabel(7, listOf())
        )
        assertFalse(s1.equivalentTo(s2))
    }

    @Test
    fun `label bijection - one label mapped to two - not equivalent`() {
        val s1 = state(
            mapOf(7 to 0),
            "foo" to NamedLabel(7, listOf()),
            "bar" to NamedLabel(7, listOf())
        )
        val s2 = state(
            mapOf(0 to 0, 1 to 0),
            "foo" to NamedLabel(0, listOf()),
            "bar" to NamedLabel(1, listOf())
        )
        assertFalse(s1.equivalentTo(s2))
    }

    @Test
    fun `same label appearing multiple times in one type forces same mapping`() {
        val s1 = state(
            mapOf(0 to 1),
            "foo" to NamedLabel(0, listOf(NamedLabel(0, listOf(Variable(0)))))
        )
        val s2 = state(
            mapOf(5 to 1),
            "foo" to NamedLabel(5, listOf(NamedLabel(5, listOf(Variable(0)))))
        )
        assertTrue(s1.equivalentTo(s2))
    }

    @Test
    fun `same label appearing nested with different inner label - not equivalent`() {
        // L0[L0[..]] cannot match L5[L6[..]]
        val s1 = state(
            mapOf(0 to 1),
            "foo" to NamedLabel(0, listOf(NamedLabel(0, listOf(Variable(0)))))
        )
        val s2 = state(
            mapOf(5 to 1, 6 to 1),
            "foo" to NamedLabel(5, listOf(NamedLabel(6, listOf(Variable(0)))))
        )
        assertFalse(s1.equivalentTo(s2))
    }

    // ----- Shape mismatches -----
    @Test
    fun `arrow vs label not equivalent`() {
        val s1 = state(mapOf(), "foo" to Arrow(Variable(0), Variable(1)))
        val s2 = state(mapOf(0 to 2), "foo" to NamedLabel(0, listOf(Variable(0), Variable(1))))
        assertFalse(s1.equivalentTo(s2))
    }

    @Test
    fun `arrow vs variable not equivalent`() {
        val s1 = state(mapOf(), "foo" to Arrow(Variable(0), Variable(1)))
        val s2 = state(mapOf(), "foo" to Variable(0))
        assertFalse(s1.equivalentTo(s2))
    }

    @Test
    fun `variable vs label not equivalent`() {
        val s1 = state(mapOf(), "foo" to Variable(0))
        val s2 = state(mapOf(0 to 0), "foo" to NamedLabel(0, listOf()))
        assertFalse(s1.equivalentTo(s2))
    }

    @Test
    fun `different label arities not equivalent`() {
        val s1 = state(mapOf(0 to 1), "foo" to NamedLabel(0, listOf(Variable(0))))
        val s2 = state(mapOf(5 to 2), "foo" to NamedLabel(5, listOf(Variable(0), Variable(1))))
        assertFalse(s1.equivalentTo(s2))
    }

    @Test
    fun `arrow branching swapped - not equivalent`() {
        // (a -> b) -> c   vs   a -> (b -> c)
        val s1 = state(
            mapOf(),
            "foo" to Arrow(Arrow(Variable(0), Variable(1)), Variable(2))
        )
        val s2 = state(
            mapOf(),
            "foo" to Arrow(Variable(0), Arrow(Variable(1), Variable(2)))
        )
        assertFalse(s1.equivalentTo(s2))
    }

    // ----- Holes -----
    @Test
    fun `TypeHole equivalent to TypeHole`() {
        val s1 = state(mapOf(), "foo" to TypeHole())
        val s2 = state(mapOf(), "foo" to TypeHole())
        assertTrue(s1.equivalentTo(s2))
    }

    @Test
    fun `TypeHole equivalent to Blank`() {
        val s1 = state(mapOf(), "foo" to TypeHole())
        val s2 = state(mapOf(), "foo" to Blank(labelOnly = true))
        assertTrue(s1.equivalentTo(s2))
    }

    @Test
    fun `Blank labelOnly equivalent to Blank not labelOnly`() {
        val s1 = state(mapOf(), "foo" to Blank(labelOnly = true))
        val s2 = state(mapOf(), "foo" to Blank(labelOnly = false))
        assertTrue(s1.equivalentTo(s2))
    }

    @Test
    fun `hole vs variable not equivalent`() {
        val s1 = state(mapOf(), "foo" to TypeHole())
        val s2 = state(mapOf(), "foo" to Variable(0))
        assertFalse(s1.equivalentTo(s2))
    }

    @Test
    fun `hole vs label not equivalent`() {
        val s1 = state(mapOf(), "foo" to TypeHole())
        val s2 = state(mapOf(0 to 0), "foo" to NamedLabel(0, listOf()))
        assertFalse(s1.equivalentTo(s2))
    }

    @Test
    fun `hole vs arrow not equivalent`() {
        val s1 = state(mapOf(), "foo" to TypeHole())
        val s2 = state(mapOf(), "foo" to Arrow(Variable(0), Variable(1)))
        assertFalse(s1.equivalentTo(s2))
    }

    @Test
    fun `holes nested inside labels - equivalent`() {
        val s1 = state(
            mapOf(0 to 2),
            "foo" to NamedLabel(0, listOf(TypeHole(), Blank(labelOnly = true)))
        )
        val s2 = state(
            mapOf(5 to 2),
            "foo" to NamedLabel(5, listOf(Blank(labelOnly = false), TypeHole()))
        )
        assertTrue(s1.equivalentTo(s2))
    }

    // ----- Symmetry on the user's example variant -----
    @Test
    fun `symmetry on complex example`() {
        val a = Variable(0)
        val b = Variable(1)
        // 'a -> 'b -> L0[L1['a, 'a], 'b]
        val s1 = state(
            mapOf(0 to 2, 1 to 2),
            "f" to Arrow(a, Arrow(b, NamedLabel(0, listOf(NamedLabel(1, listOf(a, a)), b))))
        )
        val a2 = Variable(42)
        val b2 = Variable(7)
        val s2 = state(
            mapOf(99 to 2, 100 to 2),
            "f" to Arrow(a2, Arrow(b2, NamedLabel(99, listOf(NamedLabel(100, listOf(a2, a2)), b2))))
        )
        assertTrue(s1.equivalentTo(s2))
        assertTrue(s2.equivalentTo(s1))
    }

    // ----- Order of names should not matter -----
    @Test
    fun `name iteration order does not affect equivalence`() {
        // Construct two equivalent states whose names map insertion-order differs.
        val s1Map = linkedMapOf("a" to 0, "b" to 1)
        val s2Map = linkedMapOf("b" to 1, "a" to 0)
        val s1 = SearchState(
            names = s1Map,
            types = listOf(
                NamedLabel(0, listOf(Variable(0))),
                NamedLabel(1, listOf(Variable(0), Variable(1)))
            ),
            labelArities = mapOf(0 to 1, 1 to 2)
        )
        val s2 = SearchState(
            names = s2Map,
            types = listOf(
                NamedLabel(5, listOf(Variable(7))),
                NamedLabel(8, listOf(Variable(3), Variable(4)))
            ),
            labelArities = mapOf(5 to 1, 8 to 2)
        )
        assertTrue(s1.equivalentTo(s2))
        assertTrue(s2.equivalentTo(s1))
    }

    // ----- Mixed: arrow with labels and shared vars -----
    @Test
    fun `arrow containing labels and shared vars - equivalent`() {
        // foo: L0['a] -> L0['a]
        val s1 = state(
            mapOf(0 to 1),
            "foo" to Arrow(
                NamedLabel(0, listOf(Variable(0))),
                NamedLabel(0, listOf(Variable(0)))
            )
        )
        val s2 = state(
            mapOf(9 to 1),
            "foo" to Arrow(
                NamedLabel(9, listOf(Variable(11))),
                NamedLabel(9, listOf(Variable(11)))
            )
        )
        assertTrue(s1.equivalentTo(s2))
    }

    @Test
    fun `arrow containing labels - different shared vars - not equivalent`() {
        // foo: L0['a] -> L0['a] cannot match L0['a] -> L0['b]
        val s1 = state(
            mapOf(0 to 1),
            "foo" to Arrow(
                NamedLabel(0, listOf(Variable(0))),
                NamedLabel(0, listOf(Variable(0)))
            )
        )
        val s2 = state(
            mapOf(0 to 1),
            "foo" to Arrow(
                NamedLabel(0, listOf(Variable(0))),
                NamedLabel(0, listOf(Variable(1)))
            )
        )
        assertFalse(s1.equivalentTo(s2))
    }

    // ----- Unused labelArities entries should not affect equivalence -----
    @Test
    fun `unused label in labelArities is ignored`() {
        // labelArities differs, but the unused label is not referenced by any type.
        val s1 = state(
            mapOf(0 to 0, 99 to 3),
            "foo" to NamedLabel(0, listOf())
        )
        val s2 = state(
            mapOf(5 to 0),
            "foo" to NamedLabel(5, listOf())
        )
        assertTrue(s1.equivalentTo(s2))
    }

    // ----- Deep nesting with multiple labels and vars -----
    @Test
    fun `deep nested type with multiple labels and vars - equivalent`() {
        // foo: L0[L1['a, L0['b]], L1['b, L0['a]]]
        val s1 = state(
            mapOf(0 to 2, 1 to 2),
            "foo" to NamedLabel(
                0,
                listOf(
                    NamedLabel(1, listOf(Variable(0), NamedLabel(0, listOf(Variable(1), Variable(1))))),
                    NamedLabel(1, listOf(Variable(1), NamedLabel(0, listOf(Variable(0), Variable(0)))))
                )
            )
        )
        val s2 = state(
            mapOf(10 to 2, 20 to 2),
            "foo" to NamedLabel(
                10,
                listOf(
                    NamedLabel(20, listOf(Variable(7), NamedLabel(10, listOf(Variable(8), Variable(8))))),
                    NamedLabel(20, listOf(Variable(8), NamedLabel(10, listOf(Variable(7), Variable(7)))))
                )
            )
        )
        assertTrue(s1.equivalentTo(s2))
    }
}
