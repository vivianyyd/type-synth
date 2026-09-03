package oneast

import query.App
import query.Example
import query.Examples
import query.Name
import util.IntVec

/**
 * The application structure of a fixed list of examples, with names resolved to indices into a
 * search state's types.
 *
 * Neither the examples nor the set of names change during a search, so this is built once and
 * shared by every [OneUnification] over them. Nodes are numbered so that a node's children come
 * before it, which lets a check be a single forward pass.
 */
class Program(names: Map<String, Int>, examples: List<Example>) {
    /** Which of the environment's types these examples mention, so a refinement elsewhere is free. */
    internal val usesType = BooleanArray(names.size)

    /** For an application, the node of the function; -1 for a name. */
    internal val fn = IntVec()

    /** For an application, the node of the argument; for a name, the index of its type. */
    internal val arg = IntVec()

    /** For a name, which instantiation of its type this occurrence is; -1 for an application. */
    internal val instId = IntVec()

    /** How many times a component type is instantiated by these examples. */
    internal var instantiations = 0
        private set

    internal val size
        get() = fn.size

    init {
        examples.forEach { add(it, names) }
    }

    private fun add(ex: Example, names: Map<String, Int>): Int =
        when (ex) {
            is Name -> {
                fn.add(-1)
                val type = names[ex.name] ?: error("${ex.name} not in $names")
                usesType[type] = true
                arg.add(type)
                instId.add(instantiations++)
                fn.size - 1
            }
            is App -> {
                val f = add(ex.fn, names)
                val a = add(ex.arg, names)
                fn.add(f)
                arg.add(a)
                instId.add(-1)
                fn.size - 1
            }
        }
}

/** The [Program]s of an example set, which every search state over the same names shares. */
class Programs(examples: Examples, names: Map<String, Int>) {
    val pos = Program(names, examples.posNoSubexprs)

    /** One per negative example, since each must be shown unsatisfiable on its own. */
    val neg = examples.neg.map { Program(names, listOf(it)) }
}

/**
 * Type-checks a [Program] against an [environment], and reports what that told us about the
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
 * [type] is only meaningful before any [refine], since the environment it reports against is the
 * one this was constructed with.
 */
class OneUnification(private val program: Program, private val environment: SearchState) {
    constructor(environment: SearchState, examples: List<Example>) :
            this(Program(environment.names, examples), environment)

    private val graph = TypeGraph()
    private val node = IntArray(program.size)
    private var instantiations = program.instantiations

    init {
        for (i in 0 until program.size) {
            val f = program.fn[i]
            node[i] =
                if (f < 0) instantiate(environment.types[program.arg[i]], program.instId[i])
                else graph.apply(node[f], node[program.arg[i]])
            if (node[i] == TypeGraph.NONE) break
        }
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
     * The type constructor that every instantiation of [hole] was unified with, as a label id or
     * [TypeGraph.ARROW]; null if there was none or if they disagreed. The enumerator treats those
     * two cases alike — neither says anything about the hole's shape — and asking the question this
     * way avoids building the constraint types just to compare their heads.
     */
    fun holeConstructor(hole: THole): Int? {
        if (!ok) return null
        val instances = graph.instancesOf(hole) ?: return null
        var label = TypeGraph.NONE
        var arity = -1
        for (i in 0 until instances.size) {
            val found = graph.constructorOf(instances[i])
            if (found == TypeGraph.NONE) continue
            val foundArity = graph.constructorArity(instances[i])
            if (label == TypeGraph.NONE) {
                label = found
                arity = foundArity
            } else if (label != found || arity != foundArity) return null
        }
        return if (label == TypeGraph.NONE) null else label
    }

    /**
     * The type [ex] has in this environment, or null if it does not type-check. Derived on its own,
     * so it is meaningful even for an expression whose enclosing example failed.
     */
    fun type(ex: Example): ConstraintTy? =
        graph.speculate {
            val n = typeNode(ex)
            if (n == TypeGraph.NONE) null else graph.typeAt(n)
        }

    private fun typeNode(ex: Example): Int =
        when (ex) {
            is Name -> instantiate(environment.typeOf(ex.name), instantiations++)
            is App -> {
                val f = typeNode(ex.fn)
                if (f == TypeGraph.NONE) f
                else typeNode(ex.arg).let { a ->
                    if (a == TypeGraph.NONE) a else graph.apply(f, a)
                }
            }
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
    fun mark(): Long = graph.mark()

    /** Undoes every refinement made since [mark] was taken. */
    fun rewindTo(mark: Long) = graph.rewindTo(mark)

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

/**
 * The checks the enumerator carries as it descends: the positive examples must stay satisfiable,
 * and no negative example may become satisfiable without help from a hole.
 *
 * All of them are refined and rewound together, so descending one level of the search costs one
 * refinement of each rather than a full re-check.
 */
class Checks(state: SearchState, examples: Examples) {
    private val programs = examples.programs(state.names)

    val pos = OneUnification(programs.pos, state)

    private val neg = Array(programs.neg.size) { OneUnification(programs.neg[it], state) }

    /** Whether each negative example currently type-checks without relying on any hole. */
    private val negPasses = BooleanArray(neg.size) { neg[it].passedWithNoConstraints }

    private var passing = negPasses.count { it }

    /** One saved state per search depth; see [save]. */
    private var checkpoints = arrayOfNulls<Checkpoint>(16)

    private class Checkpoint(graphs: Int, negex: Int) {
        val graphs = LongArray(graphs)
        val negPasses = BooleanArray(negex)
        var passing = 0
    }

    /** Whether some negative example type-checks without relying on any hole. */
    fun someNegexPasses() = passing > 0

    /**
     * Remembers the state of every check, so that [restore] can come back to it before the next
     * expansion at this [depth] of the search. Checkpoints are kept per depth rather than allocated
     * per call, since the search only ever returns to the depth it is currently at.
     */
    fun save(depth: Int) {
        if (depth >= checkpoints.size) checkpoints = checkpoints.copyOf(depth * 2)
        val saved =
            checkpoints[depth] ?: Checkpoint(neg.size + 1, neg.size).also { checkpoints[depth] = it }
        saved.graphs[0] = pos.mark()
        for (i in neg.indices) saved.graphs[i + 1] = neg[i].mark()
        negPasses.copyInto(saved.negPasses)
        saved.passing = passing
    }

    /** Undoes every refinement made since [save] was called at this [depth]. */
    fun restore(depth: Int) {
        val saved = checkpoints[depth]!!
        pos.rewindTo(saved.graphs[0])
        for (i in neg.indices) neg[i].rewindTo(saved.graphs[i + 1])
        saved.negPasses.copyInto(negPasses)
        passing = saved.passing
    }

    /**
     * Refines every check that mentions the type at [typeIndex] — a hole in any other type cannot
     * affect them — and reports whether the positive examples still type-check.
     */
    fun refine(typeIndex: Int, hole: THole, replacement: Type): Boolean {
        for (i in neg.indices) {
            if (!programs.neg[i].usesType[typeIndex]) continue
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
