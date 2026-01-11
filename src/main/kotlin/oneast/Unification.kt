package oneast

import query.App
import query.Example
import query.Name
import util.Counter

typealias Binding = Pair<ConstraintVariable, ConstraintTy>

/**
 * This unification does not persist state after evaluating a candidate, and cannot be used more
 * than once.
 */
class OneUnification(private val candidate: SearchState, private val exs: List<Example>) {
    private var evaluated = false
    private var error = false
    private val holeConstraints = mutableMapOf<Int, MutableList<ConstraintTy>>() // holeId

    private val insts = Counter() // Number of times any top-level type has been instantiated

    fun holeEquals(hole: Int): List<ConstraintTy> =
        if (ok()) holeConstraints[hole] ?: listOf() else listOf()

    fun ok(): Boolean {
        if (!evaluated) {
            error = exs.any { type(it) == null }
            evaluated = true
        }
        return !error
    }

    private fun type(ex: Example): ConstraintTy? =
        when (ex) {
            // instantiate immediately. later, consider doing this lazily if it's slow
            is Name -> candidate.typeOf(ex.name).instantiate(insts.get())
            is App ->
                type(ex.fn)?.let { f ->
                    type(ex.arg)?.let { arg ->
                        when (f) {
                            is ConstraintArrow -> apply(f, arg)
                            is InstantiationTy -> {
                                /* since we continue deriving constraints after seeing f, introduce
                                a bottom type which doesn't correspond to any node. once this
                                hole expands into concrete type options, we'll derive constraints
                                on the function inputs/outputs accordingly - but that must happen
                                in a future pass. */
                                holeConstraint(f, ConstraintArrow(arg, Bottom))
                                f
                            }
                            else -> null
                        }
                    }
                }
        }

    fun apply(fn: ConstraintArrow, arg: ConstraintTy): ConstraintTy? =
        unify(fn.l, arg)?.let { applyBindings(fn.r, it) }

    private fun holeConstraint(inst: InstantiationTy, t: ConstraintTy) {
        holeConstraints.getOrPut(inst.hole.id) { mutableListOf() }.add(t)
    }

    /**
     * Returns a list of bindings resulting from unifying [arg] with [param], or null if they are
     * incompatible.
     */
    fun unify(param: ConstraintTy, arg: ConstraintTy): List<Binding>? =
        when (param) {
            Bottom -> emptyList()
            is ConstraintVariable ->
                if (param in arg.variables()) null else listOf(Binding(param, arg))
            is TypeConstructor ->
                when (arg) {
                    Bottom -> emptyList()
                    is TypeConstructor -> {
                        if (param.match(arg)) {
                            var bindings: MutableList<Binding>? = mutableListOf()
                            param.params.zip(arg.params).forEach {
                                if (bindings != null) {
                                    val l = applyBindings(it.first, bindings!!)
                                    val r = applyBindings(it.second, bindings!!)
                                    val u = unify(l, r)
                                    if (u == null) bindings = null else bindings!!.addAll(u)
                                }
                            }
                            bindings
                        } else null
                    }
                    is ConstraintVariable ->
                        // e.g. a function expects param (int -> int) and we pass ('a -> 'a)
                        if (arg in param.variables()) null else listOf(Binding(arg, param))
                    is InstantiationTy -> {
                        holeConstraint(arg, param)
                        listOf()
                    }
                }
            is InstantiationTy -> {
                holeConstraint(param, arg)
                listOf()
            }
        }

    fun applyBinding(t: ConstraintTy, v: ConstraintVariable, sub: ConstraintTy): ConstraintTy {
        if (t.variables().isEmpty()) return t
        return when (t) {
            Bottom -> t
            is ConstraintVariable -> if (t == v) sub else t
            is TypeConstructor -> {
                val reboundParams = t.params.map { applyBinding(it, v, sub) }
                when (t) {
                    is ConstraintArrow -> t.copy(params = reboundParams)
                    is ConstraintLabel -> t.copy(params = reboundParams)
                }
            }
            is InstantiationTy -> error("hasConstraintVariable should have been false")
        }
    }

    fun applyBindings(t: ConstraintTy, bindings: List<Binding>): ConstraintTy =
        bindings.fold(t) { acc, (v, sub) -> applyBinding(acc, v, sub) }
}
