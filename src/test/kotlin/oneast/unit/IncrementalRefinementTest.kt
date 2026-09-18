package oneast.unit

import oneast.*
import org.junit.jupiter.api.Test
import query.Examples
import testutil.loadQueryFromFile
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

/**
 * Walks a search by hand. Every name's type starts as a single hole, and the tests fill one hole at
 * a time with expansions chosen here, the way the enumerator would.
 *
 * After every step, the incremental check is compared against a check built from scratch for the
 * resulting state, and every undo must restore exactly what was seen at that depth. On top of that,
 * each test asserts what its chosen expansions should obviously cause.
 */
class IncrementalRefinementTest {
    private val I = 0
    private val B = 1
    private val L = 2

    private fun int() = NamedLabel(I, listOf())
    private fun bool() = NamedLabel(B, listOf())
    private fun list(t: Type) = NamedLabel(L, listOf(t))
    private fun fn(from: Type, to: Type) = Arrow(from, to)
    private val a = Variable(0)
    private val b = Variable(1)

    /** cons : a -> L[a] -> L[a], as in cons.sexp and polymorphic-nil.sexp. */
    private val consType = fn(a, fn(list(a), list(a)))

    // ------------------------------------------------------------------------ cons.sexp

    private val consTruth = listOf(
        "cons" to consType,
        "Num" to int(),
        "true" to bool(),
        "Li" to list(int()),
        "LLi" to list(list(int())),
        "Lb" to list(bool()),
    )

    @Test
    fun `cons - fill every type, cons first`() {
        val walk = Walk("cons")
        consTruth.forEach { (name, type) -> walk.fillTowards(name, type) }
        walk.assertNothingOnTheWayWasPruned()
        walk.assertEveryExampleIsClassifiedCorrectly()
        walk.undoAll()
    }

    @Test
    fun `cons - fill every type, cons last`() {
        val walk = Walk("cons")
        consTruth.reversed().forEach { (name, type) -> walk.fillTowards(name, type) }
        walk.assertNothingOnTheWayWasPruned()
        walk.assertEveryExampleIsClassifiedCorrectly()
        walk.undoAll()
    }

    @Test
    fun `cons - what unification learns about the holes in cons`() {
        val walk = Walk("cons")
        consTruth.drop(1).forEach { (name, type) -> walk.fillTowards(name, type) }

        walk.fill("cons", fn(TypeHole(), TypeHole()))
        val (param, rest) = walk.holesOf("cons")
        // cons's first argument is Num in some examples and a list in others.
        assertEquals(HoleConstructor.Conflicting, walk.pos.holeConstructor(param))
        // Wherever cons is given a second argument, what it returned is applied to it.
        assertEquals(HoleConstructor.Arrow, walk.pos.holeConstructor(rest))

        walk.fill("cons", a)
        walk.fill("cons", fn(TypeHole(), TypeHole()))
        val (second, _) = walk.holesOf("cons")
        // The second argument is always some list: Li, LLi, Lb, or the result of another cons.
        assertEquals(HoleConstructor.Label(L), walk.pos.holeConstructor(second))
    }

    @Test
    fun `cons - a list of the wrong element type fails with the two clashing labels`() {
        val walk = Walk("cons")
        consTruth.filter { it.first != "Li" }.forEach { (name, type) -> walk.fillTowards(name, type) }
        walk.fill("Li", list(TypeHole()))
        assertTrue(walk.pos.ok)

        val wrong = walk.fill("Li", bool())
        assertFalse(wrong.posOk)
        assertEquals(setOf(I, B), walk.pos.badLabels())
        walk.undo()

        val right = walk.fill("Li", int())
        assertTrue(right.posOk)
        walk.assertEveryExampleIsClassifiedCorrectly()
        walk.undoAll()
    }

    // ---------------------------------------------------------------- polymorphic-nil.sexp

    private val nilTruth = listOf(
        "cons" to consType,
        "Num" to int(),
        "true" to bool(),
        "nil" to list(a),
    )

    @Test
    fun `polymorphic nil - fill every type, cons first`() {
        val walk = Walk("polymorphic-nil")
        nilTruth.forEach { (name, type) -> walk.fillTowards(name, type) }
        walk.assertNothingOnTheWayWasPruned()
        walk.assertEveryExampleIsClassifiedCorrectly()
        walk.undoAll()
    }

    @Test
    fun `polymorphic nil - fill every type, nil first`() {
        val walk = Walk("polymorphic-nil")
        nilTruth.reversed().forEach { (name, type) -> walk.fillTowards(name, type) }
        walk.assertNothingOnTheWayWasPruned()
        walk.assertEveryExampleIsClassifiedCorrectly()
        walk.undoAll()
    }

    @Test
    fun `polymorphic nil - nil must be a list, but not of any one element type`() {
        val walk = Walk("polymorphic-nil")
        nilTruth.filter { it.first != "nil" }.forEach { (name, type) -> walk.fillTowards(name, type) }

        // nil is only ever passed where cons wants a list.
        assertEquals(HoleConstructor.Label(L), walk.pos.holeConstructor(walk.holesOf("nil").single()))

        walk.fill("nil", list(TypeHole()))
        // ...but a list of Num in one example, of true in another, of lists in a third.
        val element = walk.holesOf("nil").single()
        assertEquals(HoleConstructor.Conflicting, walk.pos.holeConstructor(element))

        // So a monomorphic nil breaks a positive example.
        assertFalse(walk.fill("nil", int()).posOk)
        walk.undo()

        walk.fill("nil", a)
        walk.assertEveryExampleIsClassifiedCorrectly()
        walk.undoAll()
    }

    @Test
    fun `polymorphic nil - the examples do not rule out nil being any type at all`() {
        val walk = Walk("polymorphic-nil")
        nilTruth.filter { it.first != "nil" }.forEach { (name, type) -> walk.fillTowards(name, type) }

        // nil : a. cons alone makes every positive example type-check and every negative one fail.
        val filled = walk.fill("nil", a)
        assertTrue(filled.posOk)
        walk.assertEveryExampleIsClassifiedCorrectly()
        walk.undoAll()
    }

    // ---------------------------------------------------------------------------- harness

    /** What the search can ask a check, projected so that two equivalent checks compare equal. */
    private data class Observation(
        val posOk: Boolean,
        val holeConstructors: Map<THole, HoleConstructor>,
        val equalHoles: Set<Set<THole>>,
    )

    private inner class Walk(file: String) {
        private val examples: Examples = loadQueryFromFile(file).examples
        private val names = examples.names.withIndex().associate { it.value to it.index }
        private val labelArities = mapOf(I to 0, B to 0, L to 1)

        var state = SearchState(names, List(names.size) { TypeHole() }, labelArities)
            private set

        private val unification = OneUnification(state, examples.posNoSubexprs)
        private val before = ArrayList<SearchState>()
        private val marks = ArrayList<Int>()
        private val seen = arrayListOf(observe())

        init {
            assertEquals(fromScratch(), seen.single(), "the seed")
        }

        val pos
            get() = unification

        fun holesOf(name: String) = state.types[names.getValue(name)].allHoles()

        /** Replaces the leftmost hole in [name]'s type with [replacement]. */
        fun fill(name: String, replacement: Type): Observation {
            val index = names.getValue(name)
            val hole = state.types[index].allHoles().first()
            marks.add(unification.mark())
            before.add(state)
            val stillPasses = unification.refine(hole, replacement)
            state = state.mapTypeAtIndex(index) { it.replace(hole, replacement) }
            val now = observe()
            assertEquals(stillPasses, now.posOk)
            assertEquals(fromScratch(), now, "after $name := $replacement, in $state")
            seen.add(now)
            return now
        }

        /** Fills [name]'s leftmost hole towards [target], one constructor or variable at a time. */
        fun fillTowards(name: String, target: Type) {
            fill(name, shapeOf(target))
            when (target) {
                is Arrow -> {
                    fillTowards(name, target.l)
                    fillTowards(name, target.r)
                }
                is NamedLabel -> target.params.forEach { fillTowards(name, it) }
                is Variable,
                is THole -> {}
            }
        }

        fun undo() {
            seen.removeAt(seen.size - 1)
            state = before.removeAt(before.size - 1)
            unification.rewindTo(marks.removeAt(marks.size - 1))
            assertEquals(seen.last(), observe(), "undoing back to $state")
        }

        fun undoAll() {
            while (before.isNotEmpty()) undo()
        }

        /** The true types must never be pruned on the way to them. */
        fun assertNothingOnTheWayWasPruned() =
            seen.forEachIndexed { step, it ->
                assertTrue(it.posOk, "pruned at step $step: $it")
            }

        fun assertEveryExampleIsClassifiedCorrectly() {
            assertTrue(state.noHoles())
            examples.posNoSubexprs.forEach {
                assertTrue(OneUnification(state, listOf(it)).ok, "positive $it in $state")
            }
            examples.neg.forEach {
                assertFalse(OneUnification(state, listOf(it)).ok, "negative $it in $state")
            }
        }

        private fun observe() = observation(unification)

        private fun fromScratch() = observation(OneUnification(state, examples.posNoSubexprs))

        private fun observation(check: OneUnification): Observation {
            val holes = state.types.flatMap { it.allHoles() }
            return Observation(
                check.ok,
                holes.associateWith { check.holeConstructor(it) },
                check.equalHoles(holes).toSet(),
            )
        }
    }

    private fun shapeOf(t: Type): Type =
        when (t) {
            is Arrow -> Arrow(TypeHole(), TypeHole())
            is NamedLabel -> NamedLabel(t.label, List(t.params.size) { TypeHole() })
            is Variable -> t
            is THole -> error("targets have no holes")
        }
}
