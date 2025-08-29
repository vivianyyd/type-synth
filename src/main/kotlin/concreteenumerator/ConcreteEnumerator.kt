package concreteenumerator

import dependencyanalysis.*
import query.*
import stc.Projection
import std.SymTypeDFlat
import std.flatten
import util.*
import kotlin.math.min

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
    var hit = false
    override fun toString(): String = params.joinToString(separator = "->")
}

data class Var(val varId: Int, override val id: Int) : Node {
    override val constraint: DependencyConstraint? = null
    override fun toString(): String = "$varId"
}

class ConcreteEnumerator(
    val query: Query, contextOutline: Projection,
    /** Map from label ids to number of parameters */
    inLabels: Map<stc.L, Int>, private val dependencies: DependencyAnalysis, private val oracle: EqualityNewOracle
) {
    private val state: MutableMap<String, Node> = mutableMapOf()
    private val variablesInScope: Map<String, MutableList<Int>> = query.names.associateWith { mutableListOf() }
    private val labels = inLabels.mapKeys { (l, _) -> l.label }

    private var nextVariable = 0
    private var nextId = 0

    private val pos: MutableList<Example>
    private val neg: MutableList<Example>

    private val oldVarsToNewVars = mutableMapOf<String, Map<Pair<Int, Int>, Int>>()
    private fun varId(name: String, vid: Int, tid: Int) = oldVarsToNewVars[name]!![vid to tid]!!

    init {
        val constraints = constraints(contextOutline, dependencies)
        contextOutline.outline.forEach { (name, ty) ->
            val constrs = constraints[name]!!

            val oldVarsToNewIds = mutableMapOf<Pair<Int, Int>, Int>()
            fun SymTypeDFlat.toNode(constraint: DependencyConstraint?): Node = when (this) {
                is std.F -> F(
                    (this.args + this.rite).map { mutableListOf(it.toNode(constraint)) }, nextId++, constraint
                )
                is std.L -> L(this.label, labels[this.label]!!, nextId++, constraint)

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

        fun firstN(l: List<Example>) = l.subList(0, min(10 + query.names.size, l.size)).toMutableList()
        fun random(l: Collection<Example>) = firstN(l.shuffled())
        fun smallest(l: Collection<Example>) = firstN(l.sortedBy { it.size() })
        pos = smallest(query.posExamples)
        neg = smallest(query.negExamples)
    }


    /** While we start with all functions flattened, we might enumerate functions with functions as outputs */
    // Don't memoize this once, since we want to create new objects
    private fun filler(name: String, param: Int, constraint: DependencyConstraint?) = when (constraint) {
        null, is MustContainVariables -> {
            if (dependencies.mayHaveFresh(name, param)) {
                val new = nextVariable++
                variablesInScope[name]!!.add(new)
            }
            variablesInScope[name]!!.map { Var(it, nextId++) }
        }
        ContainsNoVariables -> listOf()
        is ContainsOnly -> listOf(Var(varId(name, constraint.vId, constraint.tId), nextId++))
    } + labels.map { L(it.key, it.value, nextId++, constraint) } + F(
        listOf(
            mutableListOf(Hole(constraint)),
            mutableListOf(Hole(constraint))
        ), nextId++, constraint
    )

    // TODO How to pick number of examples. 1/5? 20?
    private fun firstN(l: List<Example>) = l.subList(0, min(10 + query.names.size, l.size)).toMutableList()
    private fun random(l: Collection<Example>) = firstN(l.shuffled())
    private fun smallest(l: Collection<Example>) = firstN(l.sortedBy { it.size() })

    fun step(): List<Map<String, ConcreteNode>> {
        val solutions = mutableListOf<Map<String, ConcreteNode>>()

        state.forEach { (f, root) ->
            if (root is F) root.params.forEachIndexed { i, options ->
                options.forEach { it.enumerate(f, i) }  // assumes no top-level holes, a fair assumption...
            }
            else root.enumerate(f, 0)
        }
        println(state)

        val contexts = contexts(pos, neg)
        if (contexts.isNotEmpty()) {
            contexts.forEach {
                val failed = checkAll(it)
                if (failed == null) solutions.add(it)  // accumulate all valid contexts of this depth
                else (if (failed.second) pos else neg).add(failed.first)
            }
        }

        return solutions
    }

    fun Node.concretizations(): Sequence<ConcreteNode> = when (this) {
        is F -> if (params.isEmpty()) sequenceOf(ConcreteF(listOf()))
        else if (params.any { it.any { it is Hole } }) emptySequence()
        else lazySeqCartesianProduct(params.map {
            it.asSequence().flatMap { it.concretizations() }
        }).map { ConcreteF(it.toList()) }
        is L -> if (params.isEmpty()) sequenceOf(ConcreteL(this.label, listOf()))
        else if (params.any { it.any { it is Hole } }) emptySequence()
        else lazySeqCartesianProduct(params.map {
            it.asSequence().flatMap { it.concretizations() }
        }).map { ConcreteL(this.label, it.toList()) }
        is Var -> sequenceOf(ConcreteVar(this.varId))
        is Hole -> emptySequence()
    }

    val vars = mutableMapOf<ConcreteNode, Set<Int>>()
    fun ConcreteNode.vars(): Set<Int> = vars.getOrPut(this) {
        when (this) {
            is ConcreteVar -> setOf(varId)
            is ConcreteF -> params.flatMap { it.vars() }.toSet()
            is ConcreteL -> params.flatMap { it.vars() }.toSet()
        }
    }

    private fun Node.holelessCopy(): Node? = when (this) {
        is F -> {
            val p = params.map { it.mapNotNull { it.holelessCopy() }.toMutableList() }
            if (p.any { it.isEmpty() }) null
            else F(p, this.id, this.constraint)
        }
        is L -> {
            val p = params.map { it.mapNotNull { it.holelessCopy() }.toMutableList() }
            if (p.any { it.isEmpty() }) null
            else L(label, p, this.id, this.constraint)
        }
        is Var -> this
        is Hole -> null
    }

    private fun contexts(pos: List<Example>, neg: List<Example>): Set<Map<String, ConcreteNode>> {
        // TODO skip fresh variables if they can't be there.
        //  Rightmost param of F can't be fresh even if it's a HOF and parent allows - think about this more
        //  If last param is a label L<a->b> don't want to erroneously say a can be fresh just bc it's on the left
        val concreteOptions = state.mapValues { it.value.holelessCopy() }
        if (concreteOptions.values.any { it == null }) return emptySet()

        println("Concrete: $concreteOptions")
//        println(query.names)  // TODO WHY ARE THESE IN A DIFFERENT ORDER
//        val conflicts = mutableListOf<List<Int>>()

        val possTys = (concreteOptions as Map<String, Node>).map { (n, t) ->
            when (t) {
                is F -> {
                    if (t.params.isEmpty()) t.concretizations()
                    // TODO simplify this with concretizations()
                    else lazyCartesianProduct(t.params.mapIndexed { i, options ->
                        options.flatMap { it.concretizations() }.filter { node ->
                            when (val c = options.first().constraint) {
                                is MustContainVariables -> {
                                    val vars = node.vars()
                                    c.vars.all { (varId(n, it.first, it.second)) in vars }
                                }
                                is ContainsOnly -> {
                                    val vars = node.vars()
                                    vars.size == 1 && vars.single() == varId(n, c.vId, c.tId)
                                }
                                else -> true
                            }
                        }
                    }).map { ConcreteF(it.toList()) }
                }
                is L, is Var -> t.concretizations()
                is Hole -> throw Exception("Can't happen")
            }
        }
        return lazySeqCartesianProduct(possTys).map { concreteOptions.keys.zip(it).toMap() }.filter {
            checkOnly(it, pos, neg)
        }.toSet()
    }

    fun Node.enumerate(name: String, param: Int, inLabel: Boolean = false): Unit = when (this) {
        is Hole -> throw Exception("Should be handled by parent")
        is F -> if (!inLabel || this.hit) {  // Hacky way to delay functions under labels
            params.forEach { options ->
                if (options.removeAll { it is Hole }) {
                    options.addAll(filler(name, param, this.constraint))
                } else {
                    options.forEach { it.enumerate(name, param) }
                }
            }
        } else this.hit = true
        is L -> params.forEach { options ->
            if (options.removeAll { it is Hole }) {
                options.addAll(filler(name, param, this.constraint))
            } else {
                options.forEach { it.enumerate(name, param, true) }
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

    fun newApply(fn: ConcreteF, arg: ConcreteNode): ConcreteNode? {
        val result = unify(fn.params.first(), arg)?.let {
            val out = if (fn.params.size == 2) fn.params[1] else ConcreteF(fn.params.drop(1))
            applyBindings(out, it)
        }
        return result
    }

    fun type(context: Map<String, ConcreteNode>, example: Example): ConcreteNode? = when (example) {
        is Name -> context[example.name]
        is App -> type(context, example.fn).let { f ->
            type(context, example.arg)?.let { arg ->
                if (f is ConcreteF) newApply(f, arg) else null
            }
        }
    }

    private fun checkAll(context: Map<String, ConcreteNode>): Pair<Example, Boolean>? {
        val ctrPosEx = query.posExamples.firstOrNull { type(context, it) == null }
        if (ctrPosEx != null) return ctrPosEx to true
        val ctrNegEx = query.negExamples.firstOrNull { type(context, it) != null }
        if (ctrNegEx != null) return ctrNegEx to false
        return null
    }

    private fun checkOnly(
        context: Map<String, ConcreteNode>,
        pos: Collection<Example>,
        neg: Collection<Example>
    ): Boolean = pos.all { type(context, it) != null } && neg.all { type(context, it) == null }

    fun check(context: Map<String, ConcreteNode>/*, conflicts: MutableList<List<Int>>*/): Boolean {
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
//    val ids: List<Int>
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
