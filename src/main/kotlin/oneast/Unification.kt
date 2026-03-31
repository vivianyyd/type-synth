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
class OneUnification(private val candidate: SearchState, exs: List<Example>) {
    private val insts = Counter() // Number of times any top-level type has been instantiated

    private val holeConstraints = mutableMapOf<Int, MutableList<ConstraintTy>>() // holeId

    // The order of these declarations matters; [insts] and [holeConstraints] must be instantiated
    // before they are used to compute types
    val ok = exs.all { type(it) != null }

    val passedWithNoConstraints = ok && holeConstraints.isEmpty()

    fun holeEquals(hole: THole): List<ConstraintTy> = holeEquals(hole.id)

    private fun holeEquals(hole: Int): List<ConstraintTy> =
        if (ok) holeConstraints[hole] ?: listOf() else listOf()

    fun type(ex: Example): ConstraintTy? =
        when (ex) {
            // instantiate immediately. later, consider doing this lazily if it's slow
            is Name -> candidate.typeOf(ex.name).instantiate(insts.get())
            is App ->
                type(ex.fn)?.let { f ->
                    type(ex.arg)?.let { arg ->
                        when (f) {
                            is ConstraintArrow -> unify(f.l, arg)?.let { applyBindings(f.r, it) }
                            is InstantiationTy -> {
                                /* since we continue deriving constraints after seeing f, introduce
                                a bottom type which doesn't correspond to any node. once this
                                hole expands into concrete type options, we'll derive constraints
                                on the function inputs/outputs accordingly - but that must happen
                                in a future pass. */
                                holeConstraint(f, ConstraintArrow(arg, Bottom))?.let { Bottom }
                            }
                            is ConstraintVariable,
                            is Bottom -> Bottom // we are applying an unbound variable
                            else -> null
                        }
                    }
                }
        }

    private fun holeConstraint(inst: InstantiationTy, t: ConstraintTy): List<Binding>? =
        // unifying a Blank that must be a Label with an Arrow should fail
        if (inst.hole is Blank && inst.hole.labelOnly && t is ConstraintArrow) null
        else {
            holeConstraints.getOrPut(inst.hole.id) { mutableListOf() }.add(t)
            listOf()
        }

    /**
     * Returns a list of bindings resulting from unifying [arg] with [param], or null if they are
     * incompatible.
     */
    private fun unify(param: ConstraintTy, arg: ConstraintTy): List<Binding>? =
        when (param) {
            Bottom -> emptyList()
            is ConstraintVariable ->
                when (param) {
                    arg -> listOf()
                    in arg.variables() -> null
                    else -> listOf(Binding(param, arg))
                }
            is ConstraintTypeConstructor ->
                when (arg) {
                    Bottom -> emptyList()
                    is ConstraintTypeConstructor -> {
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
                        when (arg) {
                            param -> listOf()
                            in param.variables() -> null
                            else -> listOf(Binding(arg, param))
                        }
                    is InstantiationTy -> if (arg == param) listOf() else holeConstraint(arg, param)
                }
            is InstantiationTy -> if (arg == param) listOf() else holeConstraint(param, arg)
        }

    private fun applyBinding(
        t: ConstraintTy,
        v: ConstraintVariable,
        sub: ConstraintTy
    ): ConstraintTy {
        if (t.variables().isEmpty()) return t
        return when (t) {
            Bottom -> t
            is ConstraintVariable -> if (t == v) sub else t
            is ConstraintTypeConstructor -> {
                val reboundParams = t.params.map { applyBinding(it, v, sub) }
                when (t) {
                    is ConstraintArrow -> t.copy(params = reboundParams)
                    is ConstraintLabel -> t.copy(params = reboundParams)
                }
            }
            is InstantiationTy -> error("variables() should be empty")
        }
    }

    private fun applyBindings(t: ConstraintTy, bindings: List<Binding>): ConstraintTy =
        bindings.fold(t) { acc, (v, sub) -> applyBinding(acc, v, sub) }
}
