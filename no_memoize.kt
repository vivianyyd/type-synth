package concreteenumerator

import dependencyanalysis.*
import query.*
import stc.Projection
import std.SymTypeDFlat
import std.flatten
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

class Var(val vid: Int, val tid: Int) : Node {
    override val constraint: DependencyConstraint? = null
    override fun toString(): String = "${tid}_$vid"
}

//fun Node.concretizations(): List<Node> = when (this) {
//    is F -> if (params.isEmpty()) listOf(this) else naryCartesianProduct(params.map { it.flatMap { it.concretizations() } })
//        .map { F(it.map { mutableListOf(it) }, constraint) }
//    is L -> if (params.isEmpty()) listOf(this) else naryCartesianProduct(params.map { it.flatMap { it.concretizations() } })
//        .map { L(this.label, it.map { mutableListOf(it) }, constraint) }
//    is Var -> listOf(this)
//    is Hole -> listOf()
//}

fun Node.concretizations(): Sequence<Node> = when (this) {
    is F -> if (params.isEmpty()) sequenceOf(this)
    else if (params.any { it.any { it is Hole } }) emptySequence()
    else lazySeqCartesianProduct(params.map { it.asSequence().flatMap { it.concretizations() } })
        .map { F(it.map { mutableListOf(it) }, constraint) }
    is L -> if (params.isEmpty()) sequenceOf(this)
    else if (params.any { it.any { it is Hole } }) emptySequence()
    else lazySeqCartesianProduct(params.map { it.asSequence().flatMap { it.concretizations() } })
        .map { L(this.label, it.map { mutableListOf(it) }, constraint) }
    is Var -> sequenceOf(this)
    is Hole -> emptySequence()
}

fun Node.vars(): Set<Pair<Int, Int>> = when (this) {
    is Var -> setOf(vid to tid)
    is F -> params.flatMap { it.flatMap { it.vars() }.toSet() }.toSet()
    is L -> params.flatMap { it.flatMap { it.vars() }.toSet() }.toSet()
    is Hole -> setOf()
}

class ConcreteEnumerator(
    val query: Query,
    contextOutline: Projection,
    /** Map from label ids to number of parameters */
    inLabels: Map<stc.L, Int>,
    private val dependencies: DependencyAnalysis,
    private val oracle: EqualityNewOracle
) {
    private val state: MutableMap<String, Node> = mutableMapOf()
    private val variablesInScope: Map<String, MutableList<Var>> =
        query.names.associateWith { mutableListOf() }
    private val nextVar = mutableMapOf<String, Var>()
    private val labels = inLabels.mapKeys { (l, _) -> std.L(l.label) }
    private val frontier: MutableList<Node> = mutableListOf()
    private val constraints = constraints(contextOutline, dependencies)
    private val mayHaveFresh = dependencies.all.mapValues {
        it.value.third.map { it.i }
    }

    init {
        contextOutline.outline.forEach { (name, ty) ->
            val constrs = constraints[name]!!

            fun SymTypeDFlat.toNode(constraint: DependencyConstraint?): Node = when (this) {
                is std.F -> F(
                    (this.args + this.rite).map { mutableListOf(it.toNode(constraint)) },
                    constraint
                )
                is std.L -> L(this.label, labels[this]!!, constraint)

                is std.Var -> Var(this.vId, this.tId)
            }

            val outline = ty.flatten()
            state[name] = when (outline) {
                is std.F -> F(
                    (outline.args + outline.rite).mapIndexed { i, a -> mutableListOf(a.toNode(constrs[i])) },
                    null
                )
                is std.L, is std.Var -> outline.toNode(constrs[0])
            }

            fun variables(outline: SymTypeDFlat): Set<Var> = when (outline) {
                is std.F -> (outline.args.flatMap { variables(it) } + variables(outline.rite)).toSet()
                is std.L -> setOf()
                is std.Var -> setOf(Var(outline.vId, outline.tId))
            }
            variablesInScope[name]!!.addAll(variables(outline))
            val maxVar = variablesInScope[name]!!.maxByOrNull { it.vid } ?: Var(-1, query.names.indexOf(name))
            nextVar[name] = Var(maxVar.vid + 1, maxVar.tid)
        }
    }

    /** While we start with all functions flattened, we might enumerate functions with functions as outputs */
    private fun filler(name: String, param: Int, constraint: DependencyConstraint?) = when (constraint) {
        null, is MustContainVariables -> {
            if (param in mayHaveFresh[name]!!) {
                val new = nextVar[name]!!
                variablesInScope[name]!!.add(new)
                nextVar[name] = Var(new.vid + 1, new.tid)
            }
            variablesInScope[name]!!
        }
        ContainsNoVariables -> listOf()
        is ContainsOnly -> listOf(Var(constraint.vId, constraint.tId))
    } + labels.map { L(it.key.label, it.value, constraint) } +
            F(listOf(mutableListOf(Hole(constraint)), mutableListOf(Hole(constraint))), constraint)

    fun callMe(maxIterations: Int): Set<Map<String, Node>> {
        for (i in 1..maxIterations) {
            println("Depth $i")
            state.forEach { (f, root) ->
                if (root is F) root.params.forEachIndexed { i, options ->
                    options.forEach { it.enumerate(f, i) }  // assumes no top-level holes, a fair assumption...
                }
                else root.enumerate(f, 0)
            }
            val contexts = contexts()
            if (contexts.isNotEmpty()) return contexts
        }
        return setOf()
    }

    private fun Node.cantConcretize(): Boolean = when (this) {
        is Hole -> true
        is Var -> false
        is F -> params.any { it.all { it.cantConcretize() } }
        is L -> params.any { it.all { it.cantConcretize() } }
    }

    private fun Node.holelessCopy(): Node? = when (this) {
        is F -> F(params.map {
            it.filter { !it.cantConcretize() }.mapNotNull { it.holelessCopy() }.toMutableList()
        }, constraint)
        is Hole -> null
        is L -> L(label, params.map {
            it.filter { !it.cantConcretize() }.mapNotNull { it.holelessCopy() }.toMutableList()
        }, constraint)
        is Var -> this
    }

    private fun contexts(): Set<Map<String, Node>> {
        // TODO skip fresh variables if they can't be there.
        //  Rightmost param of F can't be fresh even if it's a HOF and parent allows - think about this more
        //  If last param is a label L<a->b> don't want to erroneously say a can be fresh just bc it's on the left
        val concreteOptions = state.mapValues { it.value.holelessCopy() }
        if (concreteOptions.values.any { it == null }) return emptySet()
        val possTys = (concreteOptions as Map<String, Node>).map { (n, t) ->
            when (t) {
                is F -> {
                    if (t.params.isEmpty()) sequenceOf(t)
                    else lazyCartesianProduct(t.params.mapIndexed { i, options ->
                        options.flatMap { it.concretizations() }.filter { node ->
                            if (constraints[n]!![i] is MustContainVariables)
                                (constraints[n]!![i] as MustContainVariables).vars.all { it in node.vars() }
                            else true
                        }
                    }).map { F(it.map { mutableListOf(it) }, t.constraint) }
                }
                is L, is Var -> t.concretizations()
                is Hole -> throw Exception("Can't happen")
            }
        }
        return lazySeqCartesianProduct(possTys).map { query.names.zip(it).toMap() }.filter { check(it) }.toSet()
    }

    fun Node.enumerate(name: String, param: Int): Unit = when (this) {
        is Hole -> throw Exception("Should be handled by parent")
        is F -> params.forEachIndexed { i, options ->
            if (options.removeAll { it is Hole }) {
                options.addAll(filler(name, param, this.constraint))
            } else {
                options.forEach { it.enumerate(name, param) }
            }
        }
        is L -> params.forEach { options ->
            if (options.removeAll { it is Hole }) {
                options.addAll(filler(name, param, this.constraint))
            } else {
                options.forEach { it.enumerate(name, param) }
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
