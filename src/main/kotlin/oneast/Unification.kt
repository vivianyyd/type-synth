package oneast

import query.App
import query.Example
import query.Examples
import query.Name

/**
 * Type-checks [examples] against an [environment], and reports what that told us about the
 * environment's holes.
 *
 * A hole stands for an unknown type expression, so each of its instantiations unifies like an
 * ordinary type variable — with the difference that we remember what it was equated with, since
 * that is the evidence the search uses to guess how to fill the hole.
 *
 * The check is *incremental*: refining a hole into a type is the only way a search state changes,
 * and it changes the constraints only where that hole was instantiated. So [refine] merges the new
 * structure into the graph built for the parent state, in time proportional to the number of
 * instantiations of that one hole, instead of re-deriving constraints for every example. [mark] and
 * [rewindTo] undo a refinement, so an entire DFS over refinements shares a single check.
 *
 * [type] reports against the environment this was constructed with, not against any refinement.
 */
class OneUnification(private val environment: SearchState, examples: List<Example>) {
    private val graph = TypeGraph()

    /** How many times a component type has been instantiated so far. Each use of a name is one. */
    private var instantiations = 0

    init {
        examples.all { build(it) != null }
    }

    val ok: Boolean
        get() = !graph.failed

    /** Whether the examples type-check without any hole having to stand for anything in particular. */
    val passedWithNoConstraints: Boolean
        get() = ok && !graph.anyHoleConstrained()

    /** The labels whose mismatch caused the most recent failure, if that is what caused it. */
    fun badLabels(): Set<Int> = graph.clash

    /** Everything unification determined [hole] must be equal to, one entry per instantiation. */
    fun holeEquals(hole: THole): List<ConstraintTy> {
        if (!ok) return emptyList()
        val instances = graph.instancesOf(hole) ?: return emptyList()
        val equals = ArrayList<ConstraintTy>(instances.size)
        for (i in 0 until instances.size) graph.constraintOn(instances[i])?.let { equals.add(it) }
        return equals
    }

    /**
     * The type constructor every instantiation of [hole] was unified with. Asking this way avoids
     * building the constraint types just to compare their outermost constructors.
     */
    fun holeConstructor(hole: THole): HoleConstructor {
        if (!ok) return HoleConstructor.None
        val instances = graph.instancesOf(hole) ?: return HoleConstructor.None
        var first: Int? = null
        for (i in 0 until instances.size) {
            val node = instances[i]
            if (!graph.hasConstructor(node)) continue
            if (first == null) first = node
            else if (!graph.sameConstructor(first, node)) return HoleConstructor.Conflicting
        }
        return when {
            first == null -> HoleConstructor.None
            graph.isArrow(first) -> HoleConstructor.Arrow
            else -> HoleConstructor.Label(graph.labelOf(first))
        }
    }

    /** The type [ex] has in this environment, or null if it does not type-check. */
    fun type(ex: Example): ConstraintTy? {
        val fresh = OneUnification(environment, emptyList())
        return fresh.build(ex)?.let { fresh.graph.typeAt(it) }
    }

    /** Adds [ex] to the graph. Returns the node for its type, or null if it does not type-check. */
    private fun build(ex: Example): Int? =
        when (ex) {
            is Name -> instantiate(environment.typeOf(ex.name), instantiations++)
            is App -> build(ex.fn)?.let { f -> build(ex.arg)?.let { a -> graph.apply(f, a) } }
        }

    private fun instantiate(t: Type, inst: Int): Int =
        when (t) {
            is Variable -> graph.rigid(t.v, inst)
            is Arrow -> graph.arrow(instantiate(t.l, inst), instantiate(t.r, inst))
            is NamedLabel ->
                graph.ctor(t.label, IntArray(t.params.size) { instantiate(t.params[it], inst) })
            is THole -> graph.hole(t, inst)
        }

    // ------------------------------------------------------------------ incremental refinement

    /** A point the check can later be [rewindTo]. */
    fun mark(): Int = graph.mark()

    /** Undoes every refinement made since [mark] was taken. */
    fun rewindTo(mark: Int) = graph.rewindTo(mark)

    /** Re-checks the state in which [hole] has become [replacement]. Returns whether it still [ok]s. */
    fun refine(hole: THole, replacement: Type): Boolean {
        if (graph.failed) return false
        val instances = graph.instancesOf(hole) ?: return true
        graph.retireHole(hole)
        for (i in 0 until instances.size) {
            val instance = instances[i]
            val filled = instantiate(replacement, graph.instantiationOf(instance))
            if (!graph.merge(instance, filled)) return false
        }
        return true
    }
}

/** What [OneUnification.holeConstructor] learned about the outermost constructor of a hole. */
sealed interface HoleConstructor {
    /** No instantiation of the hole was unified with a constructor. */
    object None : HoleConstructor {
        override fun toString() = "None"
    }

    /** Instantiations of the hole were unified with different constructors. */
    object Conflicting : HoleConstructor {
        override fun toString() = "Conflicting"
    }

    /** Every instantiation unified with a constructor was unified with an arrow. */
    object Arrow : HoleConstructor {
        override fun toString() = "Arrow"
    }

    /** Every instantiation unified with a constructor was unified with this label, at one arity. */
    data class Label(val label: Int) : HoleConstructor
}

/**
 * The checks the enumerator carries as it descends: the positive examples must stay satisfiable,
 * and no negative example may become satisfiable without help from a hole.
 *
 * All of them are refined and rewound together, so descending one level of the search costs one
 * refinement of each rather than a full re-check.
 */
class Checks(state: SearchState, examples: Examples) {
    val pos = OneUnification(state, examples.posNoSubexprs)

    private val neg = Array(examples.neg.size) { OneUnification(state, listOf(examples.neg[it])) }

    /** For each negative example, which of the state's types it mentions. */
    private val negMentions = Array(neg.size) { i ->
        BooleanArray(state.types.size).also { mentions ->
            examples.neg[i].names.forEach { mentions[state.names.getValue(it)] = true }
        }
    }

    /** Whether each negative example currently type-checks without relying on any hole. */
    private val negPasses = BooleanArray(neg.size) { neg[it].passedWithNoConstraints }

    private var passing = negPasses.count { it }

    /** Everything [rewindTo] needs to return every check to how it was when [mark] was called. */
    class Mark internal constructor(
        internal val pos: Int,
        internal val neg: IntArray,
        internal val negPasses: BooleanArray,
        internal val passing: Int,
    )

    /** Whether some negative example type-checks without relying on any hole. */
    fun someNegexPasses() = passing > 0

    fun mark() = Mark(pos.mark(), IntArray(neg.size) { neg[it].mark() }, negPasses.copyOf(), passing)

    /** Undoes every refinement made since [mark] was taken. */
    fun rewindTo(mark: Mark) {
        pos.rewindTo(mark.pos)
        for (i in neg.indices) neg[i].rewindTo(mark.neg[i])
        mark.negPasses.copyInto(negPasses)
        passing = mark.passing
    }

    /**
     * Refines every check that mentions the type at [typeIndex] — a hole in any other type cannot
     * affect them — and reports whether the positive examples still type-check.
     */
    fun refine(typeIndex: Int, hole: THole, replacement: Type): Boolean {
        for (i in neg.indices) {
            if (!negMentions[i][typeIndex]) continue
            neg[i].refine(hole, replacement)
            val passes = neg[i].passedWithNoConstraints
            if (passes != negPasses[i]) {
                negPasses[i] = passes
                passing += if (passes) 1 else -1
            }
        }
        return pos.refine(hole, replacement)
    }
}
