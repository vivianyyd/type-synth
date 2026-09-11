package oneast.unit

import oneast.*
import org.junit.jupiter.api.Test
import util.UnionFind
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertNull
import kotlin.test.assertTrue

/**
 * Tests for [UnionFind] as it is actually used: over [ConstraintTy], where [Leaf]s are the elements
 * and non-leaf [ConstraintTy]s are the bound types a class can resolve to.
 *
 * The single public mutator is [UnionFind.union]: `union(leaf, otherLeaf)` merges two classes, while
 * `union(leaf, nonLeafType)` binds a class to a type. We exploit that throughout — there is no
 * separate `bind` entry point.
 */
class UnionFindTest {
    /** Distinct [Leaf]s to populate the structure with. */
    private fun v(i: Int): Leaf = ConstraintVariable(i, 0)

    // Bound types: the non-leaf type constructors a class can resolve to. These dispatch `union` to
    // its binding behaviour.
    private val tInt: ConstraintTypeConstructor = ConstraintLabel(0, emptyList())
    private val tBool: ConstraintTypeConstructor = ConstraintLabel(1, emptyList())

    /** A [reconcile] that never conflicts: it keeps the left (existing) value. */
    private val keepLeft: (ConstraintTypeConstructor, ConstraintTypeConstructor) -> ConstraintTypeConstructor? =
        { a, _ -> a }

    /** A [reconcile] that always conflicts. */
    private val alwaysFail: (ConstraintTypeConstructor, ConstraintTypeConstructor) -> ConstraintTypeConstructor? =
        { _, _ -> null }

    /** A [reconcile] that combines two types into a fresh arrow. */
    private val combine: (ConstraintTypeConstructor, ConstraintTypeConstructor) -> ConstraintTypeConstructor? =
        { a, b -> ConstraintArrow(a, b) }

    // ---------------------------------------------------------------- add / find

    @Test
    fun `add returns the element itself as a fresh representative`() {
        val uf = UnionFind()
        assertEquals(v(0), uf.add(v(0)))
    }

    @Test
    fun `add is idempotent and returns the current representative`() {
        val uf = UnionFind()
        uf.add(v(0))
        uf.add(v(1))
        uf.union(v(0), v(1), keepLeft)
        val rep = uf.find(v(0))
        // Re-adding an already-merged member must not reset it; it returns its class rep.
        assertEquals(rep, uf.add(v(0)))
        assertEquals(rep, uf.add(v(1)))
    }

    @Test
    fun `find on an absent element is null`() {
        val uf = UnionFind()
        assertNull(uf.find(v(99)))
    }

    @Test
    fun `find on a present singleton returns itself`() {
        val uf = UnionFind()
        uf.add(v(0))
        assertEquals(v(0), uf.find(v(0)))
    }

    @Test
    fun `find agrees for all members of a class`() {
        val uf = UnionFind()
        uf.union(v(0), v(1), keepLeft)
        uf.union(v(1), v(2), keepLeft)
        val rep = uf.find(v(0))
        assertEquals(rep, uf.find(v(1)))
        assertEquals(rep, uf.find(v(2)))
        // The representative is one of the members.
        assertTrue(rep in uf.members(v(0)))
    }

    // ---------------------------------------------------------------- members

    @Test
    fun `members of an absent element is empty`() {
        val uf = UnionFind()
        assertEquals(emptySet(), uf.members(v(0)))
    }

    @Test
    fun `members of a singleton is just itself`() {
        val uf = UnionFind()
        uf.add(v(0))
        assertEquals(setOf(v(0)), uf.members(v(0)))
    }

    @Test
    fun `members is the union of both classes after union`() {
        val uf = UnionFind()
        uf.union(v(0), v(1), keepLeft)
        uf.union(v(2), v(3), keepLeft)
        uf.union(v(1), v(2), keepLeft)
        val expected = setOf(v(0), v(1), v(2), v(3))
        for (m in expected) assertEquals(expected, uf.members(m))
    }

    // ---------------------------------------------------------------- connected

    @Test
    fun `connected adds previously absent elements`() {
        val uf = UnionFind()
        assertFalse(uf.connected(v(0), v(1)))
        // Both must now be present as their own singletons.
        assertEquals(v(0), uf.find(v(0)))
        assertEquals(v(1), uf.find(v(1)))
    }

    @Test
    fun `connected adds an absent element even when the other is present`() {
        val uf = UnionFind()
        uf.add(v(0))
        assertFalse(uf.connected(v(0), v(1)))
        assertEquals(v(1), uf.find(v(1)))
    }

    @Test
    fun `connected is true for an element with itself`() {
        val uf = UnionFind()
        assertTrue(uf.connected(v(0), v(0)))
    }

    @Test
    fun `connected reflects unions`() {
        val uf = UnionFind()
        uf.union(v(0), v(1), keepLeft)
        assertTrue(uf.connected(v(0), v(1)))
        assertFalse(uf.connected(v(0), v(2)))
    }

    // ---------------------------------------------------------------- union: merging leaves

    @Test
    fun `union of two singletons succeeds and merges them`() {
        val uf = UnionFind()
        assertTrue(uf.union(v(0), v(1), keepLeft))
        assertTrue(uf.connected(v(0), v(1)))
        assertEquals(setOf(v(0), v(1)), uf.members(v(0)))
    }

    @Test
    fun `union of already-connected elements is a no-op success`() {
        val uf = UnionFind()
        uf.union(v(0), v(1), keepLeft)
        // reconcile must not even be consulted here.
        assertTrue(uf.union(v(0), v(1), alwaysFail))
        assertEquals(setOf(v(0), v(1)), uf.members(v(0)))
    }

    @Test
    fun `union is its own no-op when both args are the same element`() {
        val uf = UnionFind()
        assertTrue(uf.union(v(0), v(0), alwaysFail))
        assertEquals(setOf(v(0)), uf.members(v(0)))
    }

    @Test
    fun `union collapses three classes into one`() {
        val uf = UnionFind()
        uf.union(v(0), v(1), keepLeft)
        uf.union(v(2), v(3), keepLeft)
        uf.union(v(4), v(5), keepLeft)
        uf.union(v(0), v(2), keepLeft)
        uf.union(v(2), v(4), keepLeft)
        assertEquals(1, uf.classes.size)
        assertEquals(6, uf.members(v(0)).size)
    }

    @Test
    fun `union still works after a deep chain of merges`() {
        val uf = UnionFind()
        for (i in 0 until 1000) uf.union(v(i), v(i + 1), keepLeft)
        // Path compression must keep ends connected and the class whole.
        assertTrue(uf.connected(v(0), v(1000)))
        assertEquals(1001, uf.members(v(0)).size)
        assertEquals(1, uf.classes.size)
        assertEquals(uf.find(v(0)), uf.find(v(1000)))
    }

    // ---------------------------------------------------------------- union: binding to a type

    @Test
    fun `union with a non-leaf type binds the class to that type`() {
        val uf = UnionFind()
        assertTrue(uf.union(v(0), tInt, alwaysFail))
        assertEquals(tInt, uf.bound(v(0)))
        // Binding adds the element if absent.
        assertEquals(setOf(v(0)), uf.members(v(0)))
    }

    @Test
    fun `binding is visible from every member of the class`() {
        val uf = UnionFind()
        uf.union(v(0), v(1), keepLeft)
        uf.union(v(1), tInt, keepLeft)
        assertEquals(tInt, uf.bound(v(0)))
        assertEquals(tInt, uf.bound(v(1)))
    }

    @Test
    fun `rebinding to an equal type is a no-op success`() {
        val uf = UnionFind()
        uf.union(v(0), tInt, alwaysFail) // reconcile not consulted for an equal rebind
        assertTrue(uf.union(v(0), tInt, alwaysFail))
        assertEquals(tInt, uf.bound(v(0)))
    }

    @Test
    fun `rebinding to a different type reconciles and stores the result`() {
        val uf = UnionFind()
        uf.union(v(0), tInt, combine)
        assertTrue(uf.union(v(0), tBool, combine))
        assertEquals(ConstraintArrow(tInt, tBool), uf.bound(v(0)))
    }

    @Test
    fun `rebinding passes (existing, new) to reconcile in order`() {
        val uf = UnionFind()
        uf.union(v(0), tInt, combine)
        val seen = mutableListOf<Pair<ConstraintTypeConstructor, ConstraintTypeConstructor>>()
        uf.union(v(0), tBool) { a, b -> seen.add(a to b); a }
        assertEquals(listOf(tInt to tBool), seen)
    }

    @Test
    fun `a failed rebind returns false and keeps the old type`() {
        val uf = UnionFind()
        uf.union(v(0), tInt, alwaysFail)
        assertFalse(uf.union(v(0), tBool, alwaysFail))
        assertEquals(tInt, uf.bound(v(0)))
    }

    // ---------------------------------------------------------------- union: reconciling bounds on merge

    @Test
    fun `merging keeps the lone bound type when only one side is bound`() {
        val uf = UnionFind()
        uf.union(v(0), tInt, alwaysFail)
        uf.union(v(0), v(1), alwaysFail) // reconcile not needed: only one side bound
        assertEquals(tInt, uf.bound(v(1)))
    }

    @Test
    fun `merging keeps the lone bound type regardless of argument order`() {
        val uf = UnionFind()
        uf.union(v(1), tInt, alwaysFail)
        uf.union(v(0), v(1), alwaysFail) // bound side is the second argument
        assertEquals(tInt, uf.bound(v(0)))
    }

    @Test
    fun `merging reconciles two bound types via the callback`() {
        val uf = UnionFind()
        uf.union(v(0), tInt, combine)
        uf.union(v(1), tBool, combine)
        assertTrue(uf.union(v(0), v(1), combine))
        assertEquals(ConstraintArrow(tInt, tBool), uf.bound(v(0)))
    }

    @Test
    fun `a failed reconciliation on merge leaves both classes untouched`() {
        val uf = UnionFind()
        uf.union(v(0), tInt, alwaysFail)
        uf.union(v(1), tBool, alwaysFail)
        // Both sides bound, so the merge consults reconcile, which rejects.
        assertFalse(uf.union(v(0), v(1), alwaysFail))
        // Classes stay separate and keep their original bounds.
        assertFalse(uf.connected(v(0), v(1)))
        assertEquals(tInt, uf.bound(v(0)))
        assertEquals(tBool, uf.bound(v(1)))
    }

    @Test
    fun `a class can still be re-merged after a previously failed reconciliation`() {
        val uf = UnionFind()
        uf.union(v(0), tInt, alwaysFail)
        uf.union(v(1), tBool, alwaysFail)
        uf.union(v(0), v(1), alwaysFail) // fails, structure untouched
        // A subsequent merge with a tolerant reconcile should still succeed.
        assertTrue(uf.union(v(0), v(1), keepLeft))
        assertTrue(uf.connected(v(0), v(1)))
        assertEquals(tInt, uf.bound(v(0)))
    }

    @Test
    fun `merge passes existing bounds to reconcile in (a, b) order`() {
        val uf = UnionFind()
        uf.union(v(0), tInt, combine)
        uf.union(v(1), tBool, combine)
        val seen = mutableListOf<Pair<ConstraintTypeConstructor, ConstraintTypeConstructor>>()
        uf.union(v(0), v(1)) { a, b -> seen.add(a to b); a }
        assertEquals(listOf(tInt to tBool), seen)
    }

    // ---------------------------------------------------------------- bound

    @Test
    fun `bound of an absent element is null`() {
        val uf = UnionFind()
        assertNull(uf.bound(v(0)))
    }

    @Test
    fun `bound of an unbound class is null`() {
        val uf = UnionFind()
        uf.add(v(0))
        assertNull(uf.bound(v(0)))
    }

    // ---------------------------------------------------------------- classes snapshot

    @Test
    fun `classes is empty for a fresh structure`() {
        val uf = UnionFind()
        assertTrue(uf.classes.isEmpty())
    }

    @Test
    fun `classes reports one entry per equivalence class with its bound`() {
        val uf = UnionFind()
        uf.union(v(0), tInt, keepLeft)
        uf.union(v(0), v(1), keepLeft)
        uf.add(v(2)) // separate, unbound singleton
        val classes = uf.classes
        assertEquals(2, classes.size)
        val bound = classes.single { it.members == setOf(v(0), v(1)) }
        assertEquals(tInt, bound.bound)
        val free = classes.single { it.members == setOf(v(2)) }
        assertNull(free.bound)
    }

    @Test
    fun `classes is a snapshot that does not reflect later mutation`() {
        val uf = UnionFind()
        uf.add(v(0))
        uf.add(v(1))
        val snapshot = uf.classes
        uf.union(v(0), v(1), keepLeft)
        // The previously taken snapshot still shows two singleton classes.
        assertEquals(2, snapshot.size)
    }

    // ---------------------------------------------------------------- toString

    @Test
    fun `toString of an empty structure`() {
        val uf = UnionFind()
        assertEquals("UnionFind(empty)", uf.toString())
    }

    @Test
    fun `toString shows an unbound singleton without an equals`() {
        val uf = UnionFind()
        uf.add(v(0))
        assertEquals("UnionFind(\n  {${v(0)}}\n)", uf.toString())
    }

    @Test
    fun `toString shows the bound type after an equals`() {
        val uf = UnionFind()
        uf.union(v(0), tInt, keepLeft)
        assertEquals("UnionFind(\n  {${v(0)}} = $tInt\n)", uf.toString())
    }

    @Test
    fun `toString lists members and classes in a stable sorted order`() {
        // Build the same logical structure two different ways; output must match.
        val a = UnionFind().apply {
            union(v(2), v(1), keepLeft)
            union(v(1), tInt, keepLeft)
            add(v(0))
        }
        val b = UnionFind().apply {
            add(v(0))
            union(v(1), v(2), keepLeft)
            union(v(2), tInt, keepLeft)
        }
        assertEquals(a.toString(), b.toString())
        // Members are sorted within the class, and {V0-0} sorts before {V1-0, V2-0}.
        assertEquals(
            "UnionFind(\n  {${v(0)}}\n  {${v(1)}, ${v(2)}} = $tInt\n)",
            a.toString()
        )
    }
}
