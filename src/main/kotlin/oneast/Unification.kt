package oneast

import query.App
import query.Example
import query.Name
import util.IntUnionFind

/**
 * Type-checks [examples] against an [environment], and reports what that told us about the
 * environment's holes.
 *
 * A hole stands for an unknown type expression, so each of its instantiations unifies like an
 * ordinary type variable. What those variables end up equal to is the evidence the search uses to
 * guess how to fill the hole.
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

    /** Whether the examples type-check with the holes and blanks as they are. */
    val ok: Boolean
        get() = !graph.failed

    /**
     * Whether the holes and label-only blanks can be filled so that the examples type-check. Use
     * this for positive examples.
     *
     * [ok] alone is not enough, because each use of a blank unifies like a fresh variable but the
     * blank becomes one label. For example, with `x : .L`, `f : L[] -> I` and `g : M[] -> I`, the
     * example `pair (f x) (g x)` unifies, but x cannot be both L and M.
     */
    fun satisfiable(): Boolean = ok && blankClash() == null

    /**
     * The labels that caused the most recent failure: two labels that could not be unified, or two
     * labels one group of blanks would have to be. Empty if labels did not cause the failure.
     */
    fun badLabels(): Set<Int> = if (graph.failed) graph.clash else blankClash().orEmpty()

    /**
     * Checks that the label-only blanks can be given labels. Returns null if they can, and
     * otherwise the labels they disagree on (empty if a blank is unified with a function).
     *
     * Each blank becomes one label everywhere it is used. So:
     * - two blanks with uses in the same class must become the same label (transitively);
     * - all labels a group's uses are unified with must have the same name and arity;
     * - no use of a blank may be unified with a function.
     * Label arguments are not compared, since each use of a blank gets fresh arguments.
     *
     * Blanks that may be any type are not grouped: they can become a type variable, which differs
     * at each use.
     */
    private fun blankClash(): Set<Int>? {
        // Sorted so that the reported labels do not depend on hash order.
        val blanks = graph.holes().filter { it is Blank && it.labelOnly }.sortedBy { it.id }
        if (blanks.isEmpty()) return null

        // Put blanks with uses in the same class into one group.
        val groups = IntUnionFind()
        val firstBlankInClass = HashMap<Int, Int>()
        for (blank in blanks) {
            groups.add(blank.id)
            val instances = graph.instancesOf(blank)!!
            for (i in 0 until instances.size) {
                val node = instances[i]
                if (graph.hasConstructor(node) && graph.isArrow(node)) return emptySet()
                val first = firstBlankInClass.putIfAbsent(graph.find(node), blank.id)
                if (first != null) groups.union(blank.id, first)
            }
        }

        // Check that each group is unified with at most one label.
        val firstConstructorOfGroup = HashMap<Int, Int>()
        for (blank in blanks) {
            val group = groups.find(blank.id)!!
            val instances = graph.instancesOf(blank)!!
            for (i in 0 until instances.size) {
                val node = instances[i]
                if (!graph.hasConstructor(node)) continue
                val first = firstConstructorOfGroup.putIfAbsent(group, node) ?: continue
                if (!graph.sameConstructor(first, node))
                    return setOf(graph.labelOf(first), graph.labelOf(node))
            }
        }
        return null
    }

    /**
     * The unification class of each instantiation of [hole]. Opaque ids: they say only which
     * instantiations landed together, they are comparable only within this check, and only until it
     * changes.
     *
     * Two instantiations being unified does not make their holes equal — an instantiation of a hole
     * is a fresh variable, so `h1@3 == h2@4` holds with `h1 = a` and `h2 = int`. What it forces is
     * that the holes' outermost constructors agree, which for a [Blank] is the whole question,
     * because a Blank becomes a label. That is what [Search] uses this for.
     */
    fun classesOf(hole: THole): IntArray {
        if (!ok) return IntArray(0)
        val instances = graph.instancesOf(hole) ?: return IntArray(0)
        return IntArray(instances.size) { graph.find(instances[it]) }
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

    /**
     * The type [ex] has in this environment. Null if it does not type-check, or if unification did
     * not determine some part of it — see [TypeGraph.typeAt].
     */
    fun type(ex: Example): Type? {
        val fresh = OneUnification(environment, emptyList())
        return fresh.build(ex)?.let { fresh.graph.typeAt(it) }
    }

    /**
     * Whether [ex] type-checks alongside the examples already here. Leaves the check as it was, so
     * one environment can be tried against many examples without being rebuilt for each.
     */
    fun typeChecks(ex: Example): Boolean {
        val mark = mark()
        val used = instantiations
        val ok = build(ex) != null
        rewindTo(mark)
        instantiations = used
        return ok
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
    fun mark(): TypeGraph.Mark = graph.mark()

    /** Undoes every refinement made since [mark] was taken, and frees what it allocated. */
    fun rewindTo(mark: TypeGraph.Mark) = graph.rewindTo(mark)

    /**
     * Re-checks the state in which [hole] has become [replacement]. Returns whether it is still
     * [satisfiable].
     */
    fun refine(hole: THole, replacement: Type): Boolean {
        if (graph.failed) return false
        val instances = graph.instancesOf(hole) ?: return satisfiable()
        for (i in 0 until instances.size) {
            val instance = instances[i]
            val filled = instantiate(replacement, graph.instantiationOf(instance))
            if (!graph.merge(instance, filled)) return false
        }
        return satisfiable()
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
