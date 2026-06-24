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

    private val uf = UnionFind()
    private val badLabels = mutableSetOf<Int>() // Labels that were unified with mismatching labels

    // The order of these declarations matters; [insts] and [uf] must be instantiated
    // before they are used to compute types
    val ok = exs.all { type(it) != null }

    override fun toString() = uf.toString()

    fun passedWithNoConstraints(): Boolean {
        return ok &&
            uf.classes.all {
                it.bound == null &&
                    it.members.none {
                        it is InstantiationTy && it.hole is Blank && it.hole.labelOnly
                    }
            }
    }

    //    // TODO i'm slow but just tryign to make sure it runs
    //    private fun holeConstrs():
    //        Pair<Map<THole, List<ConstraintTypeConstructor>>, Map<THole, List<InstantiationTy>>> {
    //        val constrs = mutableMapOf<THole, MutableList<ConstraintTypeConstructor>>()
    //        val insts = mutableMapOf<THole, MutableList<InstantiationTy>>()
    //        uf.classes.forEach { cls ->
    //            cls.members.forEach { lf ->
    //                if (lf is InstantiationTy) {
    //                    if (cls.bound != null)
    //                        constrs.getOrPut(lf.hole) { mutableListOf() }.add(cls.bound)
    //                    insts
    //                        .getOrPut(lf.hole) { mutableListOf() }
    //                        .addAll(cls.members.filterIsInstance<InstantiationTy>())
    //                }
    //            }
    //        }
    //        return constrs to insts
    //    }

    fun boundConstructors(hole: THole): List<ConstraintTypeConstructor> =
        hole.instantiations().mapNotNull { uf.bound(it) }

    fun boundHoles(hole: THole): List<InstantiationTy> =
        hole.instantiations().flatMap { uf.members(it).filterIsInstance<InstantiationTy>() }

    fun badLabels(): Set<Int> = badLabels

    fun type(ex: Example): ConstraintTy? =
        when (ex) {
            // instantiate immediately. later, consider doing this lazily if it's slow
            is Name -> candidate.typeOf(ex.name).instantiate(insts.get())
            is App ->
                type(ex.fn)?.let { f ->
                    type(ex.arg)?.let { arg ->
                        //                        println("Applying ${ex.fn} to ${ex.arg} where fn:
                        // $f and arg: $arg")
                        when (f) {
                            is ConstraintArrow,
                            is ConstraintVariable,
                            is InstantiationTy -> {
                                val out = ConstraintVariable(Int.MAX_VALUE, insts.get())
                                if (unify(f, ConstraintArrow(arg, out)) != null) out else null
                            }
                            //                            is InstantiationTy -> {
                            //                                /* since we continue deriving
                            // constraints after seeing f, introduce
                            //                                a bottom type which doesn't correspond
                            // to any node. once this
                            //                                hole expands into concrete type
                            // options, we'll derive constraints
                            //                                on the function inputs/outputs
                            // accordingly - but that must happen
                            //                                in a future pass. */
                            //                                if (bindHole(f, ConstraintArrow(arg,
                            // Bottom))) Bottom else null
                            //                            }
                            is ConstraintLabel -> null
                        }
                    }
                }
        }

    private fun union(l: Leaf, t: Leaf) = uf.union(l, t, ::unifyConstr)

    private fun bind(l: Leaf, t: ConstraintTy) =
        0.let {
            //        println("Binding $l to $t")
            uf.union(l, t, ::unifyConstr)
        }

    private fun bindHole(inst: InstantiationTy, t: ConstraintTy): Boolean =
        // unifying a Blank that must be a Label with an Arrow should fail
        if (inst.hole is Blank && inst.hole.labelOnly && t is ConstraintArrow) false
        else bind(inst, t)

    /**
     * It is safe to cast the output of unify to a ConstraintTypeConstructor? when both inputs are
     * constructors because we know unify returns the same type as one of the inputs
     */
    private fun unifyConstr(
        p: ConstraintTypeConstructor,
        a: ConstraintTypeConstructor
    ): ConstraintTypeConstructor? = unify(p, a) as ConstraintTypeConstructor?

    /**
     * Returns a list of bindings resulting from unifying [arg] with [param], or null if they are
     * incompatible.
     */
    private fun unify(param: ConstraintTy, arg: ConstraintTy): ConstraintTy? =
        when (param) {
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
                    }
            is ConstraintTypeConstructor ->
                when (arg) {
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
