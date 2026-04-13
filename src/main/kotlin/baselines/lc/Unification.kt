package baselines.lc

/**
 * Robinson's unification algorithm for types.
 *
 * Used by the R-ASUP solver for redex-II reductions and for solving equalities.
 * Standard first-order unification over the type algebra (variables + →).
 */
object Unification {

    /**
     * Compute the most general unifier (MGU) of two types.
     *
     * @return the MGU substitution, or null if the types cannot be unified
     *         (occurs check failure or constructor mismatch)
     */
    fun unify(t1: Type, t2: Type): Substitution? {
        return unifyAccum(listOf(t1 to t2), Substitution.empty)
    }

    /**
     * Accumulating unification: process a worklist of pairs to unify.
     */
    private fun unifyAccum(
        worklist: List<Pair<Type, Type>>,
        currentSubst: Substitution
    ): Substitution? {
        if (worklist.isEmpty()) return currentSubst

        val (t1Raw, t2Raw) = worklist.first()
        val rest = worklist.drop(1)

        // Apply current substitution to both sides
        val t1 = currentSubst.apply(t1Raw)
        val t2 = currentSubst.apply(t2Raw)

        return when {
            // Same type — skip
            t1 == t2 -> unifyAccum(rest, currentSubst)

            // Variable on the left: bind it
            t1 is Type.Var -> {
                if (occursIn(t1.name, t2)) null // occurs check
                else {
                    val newSubst = Substitution(mapOf(t1.name to t2))
                    unifyAccum(rest, newSubst.compose(currentSubst))
                }
            }

            // Variable on the right: bind it
            t2 is Type.Var -> {
                if (occursIn(t2.name, t1)) null // occurs check
                else {
                    val newSubst = Substitution(mapOf(t2.name to t1))
                    unifyAccum(rest, newSubst.compose(currentSubst))
                }
            }

            // Arrow on both sides: decompose
            t1 is Type.Arrow && t2 is Type.Arrow -> {
                unifyAccum(
                    listOf(t1.domain to t2.domain, t1.codomain to t2.codomain) + rest,
                    currentSubst
                )
            }

            // Forall: for first-order unification purposes, we treat ∀ types
            // by stripping quantifiers (since in R-ASUP, specializable variables
            // can be replaced by polytypes — but the unification itself is first-order)
            // This case shouldn't normally arise in the core algorithm.
            else -> null // Type mismatch
        }
    }

    /**
     * Occurs check: does variable [name] appear free in [type]?
     */
    fun occursIn(name: String, type: Type): Boolean = when (type) {
        is Type.Var -> type.name == name
        is Type.Arrow -> occursIn(name, type.domain) || occursIn(name, type.codomain)
        is Type.Forall -> if (type.variable == name) false else occursIn(name, type.body)
    }
}
