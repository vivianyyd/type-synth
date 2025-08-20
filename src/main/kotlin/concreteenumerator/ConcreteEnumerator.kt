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

//fun Node.concretizations(): Sequence<ConcreteNode> = when (this) {
//    is F -> if (params.isEmpty()) sequenceOf(ConcreteF(listOf()))
//    else if (params.any { it.any { it is Hole } }) emptySequence()
//    else lazySeqCartesianProduct(params.map { it.asSequence().flatMap { it.concretizations() } })
//        .map { ConcreteF(it.toList()) }
//    is L -> if (params.isEmpty()) sequenceOf(ConcreteL(this.label, listOf()))
//    else if (params.any { it.any { it is Hole } }) emptySequence()
//    else lazySeqCartesianProduct(params.map { it.asSequence().flatMap { it.concretizations() } })
//        .map { ConcreteL(this.label, it.toList()) }
//    is Var -> sequenceOf(ConcreteVar(this.varId))
//    is Hole -> emptySequence()
//}

fun Node.concretizations(trace: List<Int>): Sequence<ConcreteNode> = when (this) {
    is F -> {
        if (params.isEmpty()) sequenceOf(ConcreteF(listOf(), trace + this.id))
        else if (params.any { it.any { it is Hole } }) emptySequence()
        else nodeProductIgnoreConflicts(
            params.map { it.asSequence().flatMap { it.concretizations(trace + this.id) } },
            trace + this.id,
        ).map { (children, tr) ->
            ConcreteF(
                children.toList(),
                tr + this.id
            )
        }
    }
    is L -> {
        if (params.isEmpty()) sequenceOf(ConcreteL(this.label, listOf(), trace + this.id))
        else if (params.any { it.any { it is Hole } }) emptySequence()
        else nodeProductIgnoreConflicts(
            params.map { it.asSequence().flatMap { it.concretizations(trace + this.id) } },
            trace + this.id,
        ).map { (children, tr) -> ConcreteL(this.label, children.toList(), tr + this.id) }
    }
    is Var -> sequenceOf(ConcreteVar(this.varId, trace + this.id))
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
    private val labels = inLabels.mapKeys { (l, _) -> l.label }
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

    private val pos = smallest(query.posExamples)
    private val neg = smallest(query.negExamples)

    fun step(): List<Map<String, ConcreteNode>> {
        val solutions = mutableListOf<Map<String, ConcreteNode>>()

        state.forEach { (f, root) ->
            if (root is F) root.params.forEachIndexed { i, options ->
                options.forEach { it.enumerate(f, i) }  // assumes no top-level holes, a fair assumption...
            }
            else root.enumerate(f, 0)
        }
        // Original, no CEGIS
//            val contexts = contexts(listOf(), listOf())
//            if (contexts.isNotEmpty()) return contexts
//            println(state)

        val contexts = contexts(pos, neg)
        if (contexts.isNotEmpty()) {
            contexts.forEach {
//                println("Passed subset of examples: $it")
                val failed = checkAll(it)
//                println(if (failed == null) "It's perfect" else if (failed.second) "Pos counter example" else "Neg counter example")
                if (failed == null) solutions.add(it)  // accumulate all valid contexts of this depth
                else (if (failed.second) pos else neg).add(failed.first)
            }
        }

        return solutions
    }

    private fun Node.canConcretize(): Boolean = when (this) {
        is Hole -> false
        is Var -> true
        is F -> params.all { it.any { it.canConcretize() } }
        is L -> params.all { it.any { it.canConcretize() } }
    }

    private fun Node.holelessCopy(): Node? = when (this) {
        is F -> F(params.map {
            it.filter { it.canConcretize() }.mapNotNull { it.holelessCopy() }.toMutableList()
        }, this.id, this.constraint)
        is L -> L(label, params.map {
            it.filter { it.canConcretize() }.mapNotNull { it.holelessCopy() }.toMutableList()
        }, this.id, this.constraint)
        is Var -> this
        is Hole -> null
    }

    private fun contexts(pos: List<Example>, neg: List<Example>): Set<Map<String, ConcreteNode>> {
        // TODO skip fresh variables if they can't be there.
        //  Rightmost param of F can't be fresh even if it's a HOF and parent allows - think about this more
        //  If last param is a label L<a->b> don't want to erroneously say a can be fresh just bc it's on the left
        val concreteOptions = state.mapValues { it.value.holelessCopy() }
        if (concreteOptions.values.any { it == null }) return emptySet()

//        println("Concrete: $concreteOptions")
//        println(query.names)  // TODO WHY ARE THESE IN A DIFFERENT ORDER
//        val conflicts = mutableListOf<List<Int>>()

        val conflicts = mutableListOf<List<Int>>()


        val parameters = (concreteOptions as Map<String, Node>).flatMap { (name, tree) ->
            when (tree) {
                is F -> tree.params.mapIndexed { i, options -> (name to i) to options }
                else -> listOf((name to 0) to listOf(tree))
            }
        }.toMap()

        val paramOptions = parameters.map { (param, options) ->
            val root = concreteOptions[param.first]!!.id
            options.asSequence().flatMap { it.concretizations(listOf(root)) }
        }

        val paramTypes = nodeProduct(paramOptions, listOf(), conflicts).map { parameters.keys.zip(it.first) }.map {
            it.filter { (param, node) ->
                val (name, i) = param
                if (constraints[name]!![i] is MustContainVariables)
                    (constraints[name]!![i] as MustContainVariables).vars.all {
                        (oldVarToNewVar(name, it.first, it.second)) in node.vars()
                    }
                else true
            }
        }

        val contexts = paramTypes.map {
            it.eqClasses() { (p1, _), (p2, _) -> p1.first == p2.first }.associate {
                if (it.size == 1) it.first().first.first to it.first().second
                else {
                    val params = it.sortedBy { it.first.second }.map { it.second }
                    it.first().first.first to ConcreteF(params, params.flatMap { it.ids })
                }
            }
        }

        return contexts.filter {
            println("Checking a context")
            checkOnly(it, pos, neg, conflicts)
        }.toSet()

        /*
        nodeProductIgnoreConflicts(
            params.map { it.asSequence().flatMap { it.concretizations(trace + this.id) } },
            trace + this.id,
        ).map { (children, tr) -> ConcreteL(this.label, children.toList(), tr + this.id) }
         */

//        val possTys = (concreteOptions as Map<String, Node>).map { (n, t) ->
//            when (t) {
//                is F -> {
//                    if (t.params.isEmpty()) t.concretizations(listOf(t.id))
//                    // TODO simplify this with concretizations()
//                    else lazyCartesianProduct(t.params.mapIndexed { i, options ->
//                        options.flatMap { it.concretizations(listOf(t.id)) }.filter { node ->
//                            if (constraints[n]!![i] is MustContainVariables)
//                                (constraints[n]!![i] as MustContainVariables).vars.all {
//                                    (oldVarToNewVar(n, it.first, it.second)) in node.vars()
//                                }
//                            else true
//                        }
//                    }).map { ConcreteF(it.toList(), it.flatMap { it.ids }) }
//                }
//                is L, is Var -> t.concretizations(listOf(t.id))
//                is Hole -> throw Exception("Can't happen")
//            }
//        }
//        return lazySeqCartesianProduct(possTys).map { query.names.zip(it).toMap() }
//            .filter { check(it/*, mutableListOf()*/) }.toSet()  // original, no CEGIS

//        return lazySeqCartesianProduct(possTys).map { concreteOptions.keys.zip(it).toMap() }.filter {
//            checkOnly(it, pos, neg)
//        }.toSet()

//        return nodeProduct(possTys, listOf(), conflicts).map { concreteOptions.keys.zip(it.first).toMap() }
//            .filter {
//                checkOnly(it, pos, neg, conflicts)
////                check(it, conflicts)
//            }.toSet()  // attempt at skipping conflicts
    }

    fun Node.enumerate(name: String, param: Int, inLabel: Boolean = false): Unit = when (this) {
        is Hole -> throw Exception("Should be handled by parent")
        is F -> params.forEach { options ->
            if (!inLabel || this.hit) {  // Hacky way to delay functions under labels
                if (options.removeAll { it is Hole }) {
                    options.addAll(filler(name, param, this.constraint))
                } else {
                    options.forEach { it.enumerate(name, param) }
                }
            } else {
                this.hit = true
            }
        }
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
                is ConcreteL -> ConcreteL(t.label, t.params.map { applyBinding(it, varId, sub) }, t.ids)
                is ConcreteF -> ConcreteF(t.params.map { applyBinding(it, varId, sub) }, t.ids)
                is ConcreteVar -> if (t.varId == varId) sub else t  // TODO t should never be a binding variable and hit this case; reason about it a bit more
            }
        }
    }

    fun applyBindings(t: ConcreteNode, bindings: List<Binding>): ConcreteNode =
        bindings.fold(t) { acc, (vId, sub) -> applyBinding(acc, vId, sub) }

    /** Returns a list of bindings resulting from unifying [arg] with [param], or null if they are incompatible.
     * @modifies [labelClasses]
     */
    private var unifyTotal = 0
    private var unifyHit = 0
    var unifyKeyHit = mutableMapOf<Pair<ConcreteNode, ConcreteNode>, Int>()
    private val unify = mutableMapOf<Pair<ConcreteNode, ConcreteNode>, List<Binding>?>()
    fun unify(param: ConcreteNode, arg: ConcreteNode): List<Binding>? {
//        unifyTotal++
//        if ((param to arg) in unify) {
//            unifyHit++
//            unifyKeyHit[param to arg] = unifyKeyHit[param to arg]!! + 1
//        } else unifyKeyHit[param to arg] = 0
//        if (unifyTotal == 10000000) {
//            println("Unify total $unifyTotal, hit $unifyHit, hit rate ${(unifyHit + 0.0) / unifyTotal}, size ${unify.size}")
//            println("Num keys not hit at all: ${unifyKeyHit.count { it.value == 0 }}")
//            println("Hit frequencies:")
//            println(unifyKeyHit.entries.sortedByDescending { it.value }.joinToString(separator = "\n"))
//        }
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
        val out = if (fn.params.size == 2) fn.params[1] else ConcreteF(fn.params.drop(1), fn.ids)
        applyBindings(out, it)
    }

    fun newApply(fn: ConcreteF, arg: ConcreteNode): ConcreteNode? {
        val result = unify(fn.params.first(), arg)?.let {
            val out = if (fn.params.size == 2) fn.params[1] else ConcreteF(fn.params.drop(1), fn.ids)
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
        neg: Collection<Example>,
        conflicts: MutableList<List<Int>>
    ): Boolean {
        /** Don't bother handling the case where we see a function applied more times than num params, since that means
         * some variable was bound to a function and it's just too complicated. We could track down where that variable
         * was first bound but why
         */
        fun relevantParams(ex: FlatApp): List<Pair<String, Int>>? {
            return if (ex.args.isEmpty()) listOf(ex.name to 0)
            else {
                if (context[ex.name]!! !is ConcreteF) listOf(ex.name to 0)
                else if (ex.args.size > (context[ex.name]!! as ConcreteF).params.size) null
                else {
                    val argParams = ex.args.map { relevantParams(it) }
                    if (argParams.any { it == null }) null
                    else (0 until ex.args.size).map { ex.name to it } + (argParams as List<List<Pair<String, Int>>>).flatten()
                }
            }
        }

        fun fail(example: Example) {
            val p = relevantParams(example.flatten())
            if (p != null) {
                conflicts.add(p.flatMap { (name, i) ->
                    when (val t = context[name]!!) {
                        is ConcreteF -> t.params[i]
                        is ConcreteL, is ConcreteVar -> if (i == 0) t else throw Exception("wat")
                    }.ids
                }.toSet().toList())
            }
        }
        return pos.all {
//        type(context, it) != null
            val ty = type(context, it)
            if (ty == null) fail(it)
            ty != null
        } && neg.all {
//        type(context, it) == null
            val ty = type(context, it)
            if (ty != null) fail(it)
            ty == null
        }
    }

    fun check(context: Map<String, ConcreteNode>/*, conflicts: MutableList<List<Int>>*/): Boolean {
//        fun fail(example: Example) {
//            conflicts.add(context.filter { it.key in example.names }.values.flatMap { it.ids }.toSet().toList())
//        }
        return query.posExamples.all {
            val ty = type(context, it)
//            if (ty == null) fail(it)
            ty != null
        } && query.negExamples.all {
            val ty = type(context, it)
//            if (ty != null) fail(it)
            ty == null
        }
    }
}

typealias Binding = Pair<Int, ConcreteNode>

/** A concrete type. */
sealed interface ConcreteNode {
    val hasVar: Boolean
    val ids: List<Int>
}

data class ConcreteL(val label: Int, val params: List<ConcreteNode>, override val ids: List<Int>) : ConcreteNode {
    override val hasVar = params.any { it.hasVar }
    override fun toString(): String = "L$label[${params.joinToString(separator = ",")}]"
}

data class ConcreteF(val params: List<ConcreteNode>, override val ids: List<Int>) : ConcreteNode {
    override val hasVar = params.any { it.hasVar }
    override fun toString(): String = params.joinToString(separator = "->") { if (it is ConcreteF) "($it)" else "$it" }
}

data class ConcreteVar(val varId: Int, override val ids: List<Int>) : ConcreteNode {
    override val hasVar = true
    override fun toString(): String = "$varId"
}
