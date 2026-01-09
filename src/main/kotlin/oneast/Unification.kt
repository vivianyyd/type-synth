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
    private val customConstraints = mutableListOf<Constraint>()
    private val holeConstraints = mutableMapOf<Int, MutableList<ConstraintTy>>() // holeId
    private val context: Map<String, Type> =
        TODO(
            "this way of implementing is slow so don't do it this way. just here to make things type check"
        )

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
            // for now, instantiate everything immediately. later i can think about lazy if it's
            // slow
            is Name -> context[ex.name]?.instantiate(insts.get())
            is App ->
                type(ex.fn).let { f ->
                    type(ex.arg)?.let { arg ->
                        when (f) {
                            is ConstraintArrow -> apply(f, arg)
                            is InstantiationTy -> {
                                holeConstraint(f, ConstraintArrow(arg, f))
                                // This is not actually the type, but the type is a hole, so let's
                                // just reuse the hole.
                                // This is okay because every time we commit, we start completely
                                // fresh.
                                TODO(
                                    "This is actually wrong... since we use the output of type() later," +
                                            "we derive constraints on the output of f that get erroneously misconstrued as constraints on f itself"
                                )
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
            is ConstraintVariable ->
                if (param in arg.variables()) null else listOf(Binding(param, arg))
            is TypeConstructor ->
                when (arg) {
                    is TypeConstructor -> {
                        val split = param.split(arg)
                        if (split == null) {
                            error = true
                            null // TODO check this is passed up correctly
                        } else {
                            val (equalities, custom) = split.partition { it is EqualityConstraint }
                            var bindings: MutableList<Binding>? = mutableListOf()
                            (equalities as List<EqualityConstraint>).forEach {
                                if (bindings != null) {
                                    val l = applyBindings(it.l, bindings!!)
                                    val r = applyBindings(it.r, bindings!!)
                                    val u = unify(l, r)
                                    if (u == null) bindings = null else bindings!!.addAll(u)
                                }
                            }
                            customConstraints.addAll(custom)
                            bindings
                        }
                    }
                    is ConstraintVariable -> // for example, a function expects argument (int -> int) and
                        // we pass ('a -> 'a)
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

    fun applyBinding(
        t: ConstraintTy,
        v: ConstraintVariable,
        sub: ConstraintTy
    ): ConstraintTy {
        if (t.variables().isEmpty()) return t
        return when (t) {
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

    fun constraints(): List<Constraint>? = if (ok()) customConstraints else null
}
