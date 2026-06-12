package oneast

import query.App
import query.Example
import query.Name
import util.Counter
import util.UnionFind

// typealias Binding = Pair<ConstraintVariable, ConstraintTy>

/**
 * This unification does not persist state after evaluating a candidate, and cannot be used more
 * than once.
 */
class OneUnification(private val candidate: SearchState, exs: List<Example>) {
    private val insts = Counter() // Number of times any top-level type has been instantiated

    private val uf = UnionFind<ConstraintTy>()
    private val badLabels = mutableSetOf<Int>()  // Labels that were unified with mismatching labels

    // The order of these declarations matters; [insts] and [uf] must be instantiated
    // before they are used to compute types
    val ok = exs.all { type(it) != null }

    fun passedWithNoConstraints(): Boolean{ return ok && holeToConstructors().all { it.value.isEmpty() } }

    // TODO i'm slow but just tryign to make sure it runs
    private fun holeConstrs() : Pair<Map<THole, List<ConstraintTypeConstructor>>, Map<THole, List<InstantiationTy>>> {
            val constrs = mutableMapOf<THole, MutableList<ConstraintTypeConstructor>>()
            val insts = mutableMapOf<THole, MutableList<InstantiationTy>>()
            uf.classes.forEach { cls ->
                cls.members.forEach { lf ->
                    if (lf is InstantiationTy) {
                        if (cls.bound != null && cls.bound is ConstraintTypeConstructor)
                            constrs.getOrPut(lf.hole) { mutableListOf() }.add(cls.bound)
                        insts
                            .getOrPut(lf.hole) { mutableListOf() }
                            .addAll(cls.members.filterIsInstance<InstantiationTy>())
                    }
                }
            }
            return constrs to insts
        }

    private fun holeToConstructors(): Map<THole, List<ConstraintTypeConstructor>>
        = holeConstrs().first

    private fun holeToHoles(): Map<THole, List<InstantiationTy>>
        = holeConstrs().second

    fun boundTypes(hole: THole): List<ConstraintTypeConstructor> =
        holeToConstructors()[hole] ?: listOf()

    fun boundHoles(hole: THole): List<InstantiationTy> =
        holeToHoles()[hole] ?: listOf()

    fun badLabels(): Set<Int> = badLabels

//    fun holeEquals(hole: THole): List<ConstraintTy> = TODO()

    fun type(ex: Example): ConstraintTy? =
        when (ex) {
            // instantiate immediately. later, consider doing this lazily if it's slow
            is Name -> candidate.typeOf(ex.name).instantiate(insts.get())
            is App ->
                type(ex.fn)?.let { f ->
                    type(ex.arg)?.let { arg ->
                        when (f) {
                            is ConstraintArrow -> {
                                val out = ConstraintVariable(Int.MAX_VALUE, insts.get())
                                if (unify(f, ConstraintArrow(arg, out)) != null) out else null
                            }
                            is InstantiationTy -> {
                                /* since we continue deriving constraints after seeing f, introduce
                                a bottom type which doesn't correspond to any node. once this
                                hole expands into concrete type options, we'll derive constraints
                                on the function inputs/outputs accordingly - but that must happen
                                in a future pass. */
                                if (bindHole(f, ConstraintArrow(arg, Bottom))) Bottom else null
                            }
                            is ConstraintVariable,
                            is Bottom -> Bottom // we are applying an unbound variable
                            else -> null
                        }
                    }
                }
        }

    private fun union(l: Leaf, t: Leaf) = uf.union(l, t, ::unify)

    private fun bind(l: Leaf, t: ConstraintTy) = uf.bind(l, t, ::unify)

    private fun bindHole(inst: InstantiationTy, t: ConstraintTy): Boolean =
        // unifying a Blank that must be a Label with an Arrow should fail
        if (inst.hole is Blank && inst.hole.labelOnly && t is ConstraintArrow) false
        else bind(inst, t)

    /**
     * Returns a list of bindings resulting from unifying [arg] with [param], or null if they are
     * incompatible.
     */
    private fun unify(param: ConstraintTy, arg: ConstraintTy): ConstraintTy? =
        when (param) {
            Bottom -> arg
            is ConstraintVariable ->
                if (param in arg.variables()) null
                else
                    when (arg) {
                        is Leaf -> {
                            if (union(param, arg)) param else null
                        }
                        is ConstraintTypeConstructor -> {
                            if (bind(param, arg)) param else null
                        }
                        Bottom -> param
                    }
            is ConstraintTypeConstructor ->
                when (arg) {
                    Bottom -> param
                    is ConstraintTypeConstructor -> {
                        if (param.match(arg)) {
                            var fail = false
                            param.params.zip(arg.params).forEach {
                                if (unify(it.first, it.second) == null) fail = true
                            }
                            if (fail) null else param
                        } else {
                            if (param is ConstraintLabel && arg is ConstraintLabel) {
                                badLabels.add(param.label)
                                badLabels.add(arg.label)
                            }
                            null
                        }
                    }
                    is ConstraintVariable ->
                        // e.g. a function expects param (int -> int) and we pass ('a -> 'a)
                        if (arg in param.variables()) null else if (bind(arg, param)) arg else null
                    is InstantiationTy -> if (bindHole(arg, param)) param else null
                }
            is InstantiationTy -> if (bindHole(param, arg)) arg else null
        }
}
