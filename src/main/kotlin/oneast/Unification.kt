package oneast

import query.App
import query.Example
import query.Name
import util.Counter

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

    fun holeEquals(hole: THole): List<ConstraintTy> = holeEquals(hole.id)

    private fun holeEquals(hole: Int): List<ConstraintTy> =
        if (ok) holeConstraints[hole]?.map { prune(it) } ?: listOf() else listOf()

    fun type(ex: Example): ConstraintTy? =
        when (ex) {
            // instantiate immediately. later, consider doing this lazily if it's slow
            is Name -> candidate.typeOf(ex.name).instantiate(insts.get())
            is App ->
                type(ex.fn)?.let { f ->
                    type(ex.arg)?.let { arg ->
                        when (f) {
                            is ConstraintArrow -> unify(f.l, arg)?.let { f.r }
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

    private fun holeConstraint(inst: InstantiationTy, t: ConstraintTy): Unit? =
        // unifying a Blank that must be a Label with an Arrow should fail
        if (inst.hole is Blank && inst.hole.labelOnly && prune(t) is ConstraintArrow) null
        else {
            holeConstraints.getOrPut(inst.hole.id) { mutableListOf() }.add(t)
            Unit
        }

    private fun occurs(v: ConstraintVariable, t: ConstraintTy): Boolean {
        val t = prune(t)
        return when (t) {
            Bottom,
            is InstantiationTy -> false
            is ConstraintVariable -> t.binding == v.binding
            is ConstraintTypeConstructor -> t.params.any { occurs(v, it) }
        }
    }

    private fun bind(v: ConstraintVariable, t: ConstraintTy): Unit? {
        require(v.binding is Unbound)
        if (occurs(v, t)) return null
        v.binding = Link(t)
        return Unit
    }

    private fun prune(t: ConstraintTy): ConstraintTy {
        return if (t is ConstraintVariable && t.binding is Link) {
            val tt = prune((t.binding as Link).t)
            t.binding = Link(tt)
            tt
        } else t
    }

    /**
     * Returns a list of bindings resulting from unifying [arg] with [param], or null if they are
     * incompatible.
     */
    private fun unify(param: ConstraintTy, arg: ConstraintTy): Unit? {
        val param = prune(param)
        val arg = prune(arg)
        return when (param) {
            Bottom -> Unit
            is ConstraintVariable ->
                when (param) {
                    arg -> Unit
                    else -> bind(param, arg)
                }
            is ConstraintTypeConstructor ->
                when (arg) {
                    Bottom -> Unit
                    is ConstraintTypeConstructor -> {
                        if (param.match(arg)) {
                            var result: Unit? = Unit
                            param.params.zip(arg.params).forEach {
                                if (result != null) result = unify(it.first, it.second)
                            }
                            result
                        } else null
                    }
                    is ConstraintVariable ->
                        // e.g. a function expects param (int -> int) and we pass ('a -> 'a)
                        when (arg) {
                            param -> Unit
                            else -> bind(arg, param)
                        }
                    is InstantiationTy -> if (arg == param) Unit else holeConstraint(arg, param)
                }
            is InstantiationTy -> if (arg == param) Unit else holeConstraint(param, arg)
        }
    }
}
