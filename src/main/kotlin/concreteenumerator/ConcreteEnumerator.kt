package concreteenumerator

import ContainsNoVariables
import ContainsOnly
import DependencyAnalysis
import DependencyConstraint
import query.*
import std.SymTypeDFlat
import util.*

sealed interface Node {
    val constraint: DependencyConstraint?
}

class Hole(override val constraint: DependencyConstraint?) : Node {
    override fun toString(): String = "_"
}

class L(
    val label: Int,
    val params: List<MutableList<Node>>,
    override val constraint: DependencyConstraint?
) : Node {
    constructor(label: Int, numParams: Int, constraint: DependencyConstraint? = null) :
            this(label, (0 until numParams).map { mutableListOf(Hole(constraint)) }, constraint)

    override fun toString(): String = "L$label(${params.joinToString(separator = ",")})"
}

class F(
    val params: List<MutableList<Node>>,
    override val constraint: DependencyConstraint?
) : Node {
    override fun toString(): String = params.joinToString(separator = "->")
}

class Var(val vid: Int, val tid: Int, override val constraint: DependencyConstraint?) : Node {
    override fun toString(): String = "${tid}_$vid"
}

fun Node.concretizations(): List<Node> = when (this) {
    is F -> if (params.isEmpty()) listOf(this) else naryCartesianProduct(params.map { it.flatMap { it.concretizations() } })
        .map { F(it.map { mutableListOf(it) }, constraint) }
    is L -> if (params.isEmpty()) listOf(this) else naryCartesianProduct(params.map { it.flatMap { it.concretizations() } })
        .map { L(this.label, it.map { mutableListOf(it) }, constraint) }
    is Var -> listOf(this)
    is Hole -> listOf()
}

class ConcreteEnumerator(
    val query: Query,
    contextOutline: Map<String, SymTypeDFlat>,
    /** Map from label ids to number of parameters */
    private val labels: Map<Int, Int>,
    private val dependencies: DependencyAnalysis,
    private val oracle: EqualityNewOracle
) {
    private val state: MutableMap<String, Node> = mutableMapOf()
    private val variablesInScope: Map<String, MutableList<Pair<Int, Int>>> =
        query.names.associateWith { mutableListOf() }

    private val frontier: MutableList<Node> = mutableListOf()

    init {
        contextOutline.forEach { (name, outline) ->
            val constraints = dependencies.constraints(name)

            fun SymTypeDFlat.toNode(constraint: DependencyConstraint?): Node = when (this) {
                is std.F ->
                    F(
                        (this.args + this.rite).map { mutableListOf(it.toNode(constraint)) },
                        constraint
                    )
                is std.L -> {
                    L(this.label, labels[this.label]!!, constraints[0])
                }
                is std.Var -> Var(this.vId, this.tId, constraint)
            }

            state[name] = when (outline) {
                is std.F ->
                    F(
                        (outline.args + outline.rite).mapIndexed { i, a -> mutableListOf(a.toNode(constraints[i])) },
                        null
                    )
                is std.L, is std.Var ->
                    outline.toNode(constraints[0])
            }

            fun variables(outline: SymTypeDFlat): Set<Pair<Int, Int>> = when (outline) {
                is std.F -> (outline.args.flatMap { variables(it) } + variables(outline.rite)).toSet()
                is std.L -> setOf()
                is std.Var -> setOf(outline.vId to outline.tId)
            }
            variablesInScope[name]!!.addAll(variables(outline))
        }
    }

    /** While we start with all functions flattened, we might enumerate functions with functions as outputs */
    private fun filler(name: String, constraint: DependencyConstraint?) = when (constraint) {
        null -> variablesInScope[name]!!.map { Var(it.first, it.second, null) }
        ContainsNoVariables -> listOf()
        is ContainsOnly -> listOf(Var(constraint.vId, constraint.tId, null))
    } + labels.map { L(it.key, it.value, constraint) } +
            F(listOf(mutableListOf(Hole(constraint)), mutableListOf(Hole(constraint))), constraint)

    fun callMe(iterations: Int): Map<String, Node> {
        repeat(iterations) { state.forEach { (f, root) -> root.enumerate(f) } }
        return state
    }

    fun contexts(): Set<Map<String, Node>> {
        val possTys = state.map { it.value.concretizations() }
        return naryCartesianProduct(possTys).map { query.names.zip(it).toMap() }.toSet()
    }

    fun Node.enumerate(name: String): Unit = when (this) {
        is Hole -> throw Exception("Should be handled by parent")
        is F -> params.forEach { options ->
            if (options.removeAll { it is Hole }) {
                options.addAll(filler(name, this.constraint))
            } else {
                options.forEach { it.enumerate(name) }
            }
        }
        is L -> params.forEach { options ->
            if (options.removeAll { it is Hole }) {
                options.addAll(filler(name, this.constraint))
            } else {
                options.forEach { it.enumerate(name) }
            }
        }
        is Var -> {}
    }


    fun applyBinding(
        t: Node,
        varId: Int,
        tId: Int,
        sub: Node
    ): Node =
        when (t) {
            is Hole -> throw Exception("Hole in concrete type")
            is L -> L(t.label, t.params.map { mutableListOf(applyBinding(it.first(), varId, tId, sub)) }, t.constraint)
            is F -> F(t.params.map { mutableListOf(applyBinding(it.first(), varId, tId, sub)) }, t.constraint)
            is Var -> if (t.vid == varId && t.tid == tId) sub else t  // TODO t should never be a binding variable and hit this case; reason about it a bit more
        }

    fun applyBindings(t: Node, bindings: List<Binding>): Node =
        bindings.fold(t) { acc, (vId, tId, sub) -> applyBinding(acc, vId, tId, sub) }

    /*
    TODO {f=0_0 -> 0_0, g=1_0 -> 1_0, h=(2_0 -> 2_0) -> 2_0, a=L} with example (h f)
     Under current impl, the second 2_0 gets bound to VB(0_0), although we want it to be a reference.
     Do we need VB/VR separation at all?
     Once we fix this, make sure to copy to the sketch version of unify
     */
    /** Returns a list of bindings resulting from unifying [arg] with [param], or null if they are incompatible.
     * @modifies [labelClasses]
     * */
    fun unify(param: Node, arg: Node): List<Binding>? =
        when (param) {
            is Var -> listOf(Binding(param.vid, param.tid, arg))
            is L -> when (arg) {
                is L -> {
                    if (param.label != arg.label) null
                    else {
                        var bindings: MutableList<Binding>? = mutableListOf()
                        param.params.indices.forEach {
                            if (bindings != null) {
                                val p = applyBindings(param.params[it].first(), bindings!!)
                                val a = applyBindings(arg.params[it].first(), bindings!!)
                                val u = unify(p, a)
                                if (u == null) bindings = null else bindings!!.addAll(u)
                            }
                        }
                        bindings
                    }
                }
                is F, is Var, is Hole -> null
            }
            is F -> when (arg) {
                is L, is Var, is Hole -> null
                is F -> {
                    var bindings: MutableList<Binding>? = mutableListOf()
                    param.params.indices.forEach {
                        if (bindings != null) {
                            val p = applyBindings(param.params[it].first(), bindings!!)
                            val a = applyBindings(arg.params[it].first(), bindings!!)
                            val u = unify(p, a)
                            if (u == null) bindings = null else bindings!!.addAll(u)
                        }
                    }
                    bindings
                }
            }
            is Hole -> throw Exception("Invariant broken")
        }

    /**
     * Returns the output type of [fn] on input [arg] with no free variables, or null if [arg] is invalid for [fn].
     * @modifies [labelClasses]
     */
    fun apply(fn: F, arg: Node): Node? =
        unify(fn.params.first().first(), arg)?.let {
            val out = if (fn.params.size == 2) fn.params[1].first() else F(fn.params.drop(1), fn.constraint)
            applyBindings(out, it)
        }

    fun type(context: Map<String, Node>, example: Example): Node? = when (example) {
        is Name -> context[example.name]
        is App -> type(context, example.fn).let { f ->
            type(context, example.arg)?.let { arg ->
                if (f is F) apply(f, arg) else null
            }
        }
    }

    fun check(context: Map<String, Node>): Boolean =
        query.posExamples.all { type(context, it) != null } && query.negExamples.all { type(context, it) == null }
}

typealias Binding = Triple<Int, Int, Node>
