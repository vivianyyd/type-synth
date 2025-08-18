package concreteenumerator

import dependencyanalysis.*
import query.*
import stc.Projection
import std.SymTypeDFlat
import std.flatten
import util.*

sealed interface Node {
    val constraint: DependencyConstraint?
    val id: Int
}

// These used to be classes instead of data classes but I don't really remember why
data class Hole(override val constraint: DependencyConstraint?) : Node {
    override val id = Int.MAX_VALUE  // Not sure about this
    override fun toString(): String = "_"
}

data class L(
    val label: Int,
    val params: List<MutableList<Node>>,
    override val id: Int,
    override val constraint: DependencyConstraint?
) : Node {
    constructor(label: Int, numParams: Int, id: Int, constraint: DependencyConstraint? = null) : this(
        label,
        (0 until numParams).map { mutableListOf(Hole(constraint)) },
        id,
        constraint
    )

    override fun toString(): String = "L$label(${params.joinToString(separator = ",")})"
}

data class F(
    val params: List<MutableList<Node>>, override val id: Int, override val constraint: DependencyConstraint?
) : Node {
    override fun toString(): String = params.joinToString(separator = "->")
}

data class Var(val varId: Int, override val id: Int) : Node {
    override val constraint: DependencyConstraint? = null
    override fun toString(): String = "$varId"
}

/** Immutable copy of a Node which can be used as a key in a memo table. */
sealed interface NodeSnapshot

// These used to be classes instead of data classes but I don't really remember why
object HoleSnapshot : NodeSnapshot {
    override fun toString(): String = "_"
}

data class LSnapshot(val label: Int, val params: List<List<NodeSnapshot>>) : NodeSnapshot {
    override fun toString(): String = "L$label(${params.joinToString(separator = ",")})"
}

data class FSnapshot(val params: List<List<NodeSnapshot>>) : NodeSnapshot {
    override fun toString(): String = params.joinToString(separator = "->")
}

data class VarSnapshot(val varId: Int) : NodeSnapshot {
    override fun toString(): String = "$varId"
}

private fun List<MutableList<Node>>.snapshot(): List<List<NodeSnapshot>> = this.map { it.map { it.snapshot() } }

private fun Node.snapshot(): NodeSnapshot = when (this) {
    is L -> LSnapshot(this.label, this.params.snapshot())
    is F -> FSnapshot(this.params.snapshot())
    is Hole -> HoleSnapshot
    is Var -> VarSnapshot(this.varId)
}

val concretizations = mutableMapOf<NodeSnapshot, Sequence<ConcreteNode>>()
fun NodeSnapshot.concretizations(): Sequence<ConcreteNode> = concretizations.getOrPut(this) {
    when (this) {
        is FSnapshot -> if (params.isEmpty()) sequenceOf(ConcreteF(listOf()))
        else if (params.any { it.any { it is HoleSnapshot } }) emptySequence()
        else lazySeqCartesianProduct(params.map { it.asSequence().flatMap { it.concretizations() } })
            .map { ConcreteF(it.map { it }) }
        is LSnapshot -> if (params.isEmpty()) sequenceOf(ConcreteL(this.label, listOf()))
        else if (params.any { it.any { it is HoleSnapshot } }) emptySequence()
        else lazySeqCartesianProduct(params.map { it.asSequence().flatMap { it.concretizations() } })
            .map { ConcreteL(this.label, it.map { it }) }
        is VarSnapshot -> sequenceOf(ConcreteVar(this.varId))
        is HoleSnapshot -> emptySequence()
    }
}

val vars = mutableMapOf<ConcreteNode, Set<Int>>()
fun ConcreteNode.vars(): Set<Int> = vars.getOrPut(this) {
    when (this) {
        is ConcreteVar -> setOf(varId)
        is ConcreteF -> params.flatMap { it.vars() }.toSet()
        is ConcreteL -> params.flatMap { it.vars() }.toSet()
    }
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
    private val variablesInScope: Map<String, MutableList<Int>> = query.names.associateWith { mutableListOf() }
    private var nextVariable = 0
    private val labels = inLabels.mapKeys { (l, _) -> std.L(l.label) }
    private val frontier: MutableList<Node> = mutableListOf()
    private var nextId = 0
    private val constraints = constraints(contextOutline, dependencies)
    private val mayHaveFresh = dependencies.all.mapValues {
        it.value.third.map { it.i }
    }
    private val oldVarsToNewVars = mutableMapOf<String, Map<Pair<Int, Int>, Int>>()

    init {
        contextOutline.outline.forEach { (name, ty) ->
            val constrs = constraints[name]!!

            val oldVarsToNewIds = mutableMapOf<Pair<Int, Int>, Int>()
            fun SymTypeDFlat.toNode(constraint: DependencyConstraint?): Node = when (this) {
                is std.F -> F(
                    (this.args + this.rite).map { mutableListOf(it.toNode(constraint)) }, nextId++, constraint
                )
                is std.L -> L(this.label, labels[this]!!, nextId++, constraint)

                is std.Var -> Var(oldVarsToNewIds.getOrPut(this.vId to this.tId) { nextVariable++ }, nextId++)
            }

            val outline = ty.flatten()
            state[name] = when (outline) {
                is std.F -> F(
                    (outline.args + outline.rite).mapIndexed { i, a -> mutableListOf(a.toNode(constrs[i])) },
                    nextId++,
                    null
                )
                is std.L, is std.Var -> outline.toNode(constrs[0])
            }
            variablesInScope[name]!!.addAll(oldVarsToNewIds.values)
            oldVarsToNewVars[name] = oldVarsToNewIds
        }
    }

    private fun oldVarToNewVar(name: String, vid: Int, tid: Int) = oldVarsToNewVars[name]!![vid to tid]!!

    /** While we start with all functions flattened, we might enumerate functions with functions as outputs */
    // Don't memoize this once, since we want to create new objects
    private fun filler(name: String, param: Int, constraint: DependencyConstraint?) = when (constraint) {
        null, is MustContainVariables -> {
            if (param in mayHaveFresh[name]!!) {
                val new = nextVariable++
                variablesInScope[name]!!.add(new)
            }
            variablesInScope[name]!!.map { Var(it, nextId++) }
        }
        ContainsNoVariables -> listOf()
        is ContainsOnly -> listOf(Var(oldVarToNewVar(name, constraint.vId, constraint.tId), nextId++))
    } + labels.map { L(it.key.label, it.value, nextId++, constraint) } + F(
        listOf(
            mutableListOf(Hole(constraint)),
            mutableListOf(Hole(constraint))
        ), nextId++, constraint
    )

    fun callMe(maxIterations: Int): Set<Map<String, ConcreteNode>> {
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

    private fun Node.canConcretize(): Boolean = when (this) {
        is Hole -> false
        is Var -> true
        is F -> params.all { it.any { it.canConcretize() } }
        is L -> params.all { it.any { it.canConcretize() } }
    }

    private fun Node.holelessCopy(): NodeSnapshot? = when (this) {
        is F -> FSnapshot(params.map {
            it.filter { it.canConcretize() }.mapNotNull { it.holelessCopy() }
        })
        is L -> LSnapshot(label, params.map {
            it.filter { it.canConcretize() }.mapNotNull { it.holelessCopy() }
        })
        is Var -> this.snapshot()
        is Hole -> null
    }

    private fun contexts(): Set<Map<String, ConcreteNode>> {
        // TODO skip fresh variables if they can't be there.
        //  Rightmost param of F can't be fresh even if it's a HOF and parent allows - think about this more
        //  If last param is a label L<a->b> don't want to erroneously say a can be fresh just bc it's on the left
        val concreteOptions = state.mapValues { it.value.holelessCopy() }
        if (concreteOptions.values.any { it == null }) return emptySet()
        val possTys = (concreteOptions as Map<String, NodeSnapshot>).map { (n, t) ->
            when (t) {
                is FSnapshot -> {
                    if (t.params.isEmpty()) t.concretizations()
                    // TODO simplify this with concretizations()
                    else lazyCartesianProduct(t.params.mapIndexed { i, options ->
                        options.flatMap { it.concretizations() }.filter { node ->
                            if (constraints[n]!![i] is MustContainVariables)
                                (constraints[n]!![i] as MustContainVariables).vars.all {
                                    (oldVarToNewVar(n, it.first, it.second)) in node.vars()
                                }
                            else true
                        }
                    }).map { ConcreteF(it.map { it }) }
                }
                is LSnapshot, is VarSnapshot -> t.concretizations()
                is HoleSnapshot -> throw Exception("Can't happen")
            }
        }
        return lazySeqCartesianProduct(possTys).map { query.names.zip(it).toMap() }.filter { check(it) }.toSet()
    }

    // TODO will this be faster if we store a frontier instead of iterating down the tree every round?
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

    private val applyBinding = mutableMapOf<Triple<ConcreteNode, Int, ConcreteNode>, ConcreteNode>()
    fun applyBinding(
        t: ConcreteNode,
        varId: Int,
        sub: ConcreteNode
    ): ConcreteNode {
        if (!t.hasVar) return t
        return applyBinding.getOrPut(Triple(t, varId, sub)) {
            when (t) {
                is ConcreteL -> ConcreteL(t.label, t.params.map { applyBinding(it, varId, sub) })
                is ConcreteF -> ConcreteF(t.params.map { applyBinding(it, varId, sub) })
                is ConcreteVar -> if (t.varId == varId) sub else t  // TODO t should never be a binding variable and hit this case; reason about it a bit more
            }
        }
    }

    fun applyBindings(t: ConcreteNode, bindings: List<Binding>): ConcreteNode =
        bindings.fold(t) { acc, (vId, sub) -> applyBinding(acc, vId, sub) }

    /** Returns a list of bindings resulting from unifying [arg] with [param], or null if they are incompatible.
     * @modifies [labelClasses]
     */
    private val unify = mutableMapOf<Pair<ConcreteNode, ConcreteNode>, List<Binding>?>()
    fun unify(param: ConcreteNode, arg: ConcreteNode): List<Binding>? {
        // We can't simply call getOrPut, since getOrPut runs code if map has null as value.
        // Then we'd do duplicate computations for all bad parameter-argument pairs
        if ((param to arg) in unify) return unify[param to arg]
        val result = when (param) {
            is ConcreteVar -> listOf(Binding(param.varId, arg))
            is ConcreteL -> when (arg) {
                is ConcreteL -> {
                    if (param.label != arg.label) null
                    else {
                        var bindings: MutableList<Binding>? = mutableListOf()
                        param.params.indices.forEach {
                            if (bindings != null) {
                                val p = applyBindings(param.params[it], bindings!!)
                                val a = applyBindings(arg.params[it], bindings!!)
                                val u = unify(p, a)
                                if (u == null) bindings = null else bindings!!.addAll(u)
                            }
                        }
                        bindings
                    }
                }
                is ConcreteF, is ConcreteVar -> null
            }
            is ConcreteF -> when (arg) {
                is ConcreteL, is ConcreteVar -> null
                is ConcreteF -> {
                    var bindings: MutableList<Binding>? = mutableListOf()
                    param.params.indices.forEach {
                        if (bindings != null) {
                            val p = applyBindings(param.params[it], bindings!!)
                            val a = applyBindings(arg.params[it], bindings!!)
                            val u = unify(p, a)
                            if (u == null) bindings = null else bindings!!.addAll(u)
                        }
                    }
                    bindings
                }
            }
        }
        unify[param to arg] = result
        return result
    }

    /**
     * Returns the output type of [fn] on input [arg] with no free variables, or null if [arg] is invalid for [fn].
     * @modifies [labelClasses]
     */
    fun apply(fn: ConcreteF, arg: ConcreteNode): ConcreteNode? = unify(fn.params.first(), arg)?.let {
        val out = if (fn.params.size == 2) fn.params[1] else ConcreteF(fn.params.drop(1))
        applyBindings(out, it)
    }

    fun type(context: Map<String, ConcreteNode>, example: Example): ConcreteNode? = when (example) {
        is Name -> context[example.name]
        is App -> type(context, example.fn).let { f ->
            type(context, example.arg)?.let { arg ->
                if (f is ConcreteF) apply(f, arg) else null
            }
        }
    }

    fun check(context: Map<String, ConcreteNode>): Boolean {
        return query.posExamples.all {
            type(context, it) != null
        } && query.negExamples.all {
            type(context, it) == null
        }
    }
}

typealias Binding = Pair<Int, ConcreteNode>

/** A concrete type. */
sealed interface ConcreteNode {
    val hasVar: Boolean
}

data class ConcreteL(val label: Int, val params: List<ConcreteNode>) : ConcreteNode {
    override val hasVar = params.any { it.hasVar }
    override fun toString(): String = "L$label[${params.joinToString(separator = ",")}]"
}

data class ConcreteF(val params: List<ConcreteNode>) : ConcreteNode {
    override val hasVar = params.any { it.hasVar }
    override fun toString(): String = params.joinToString(separator = "->") { if (it is ConcreteF) "($it)" else "$it" }
}

data class ConcreteVar(val varId: Int) : ConcreteNode {
    override val hasVar = true
    override fun toString(): String = "$varId"
}
