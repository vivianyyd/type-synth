package baselines.lc

/**
 * Phase 4: R-ASUP Solution (Section 3.4)
 *
 * Solves the R-ASUP instance via the redex procedure:
 *
 * 1. Solve equalities using Robinson's unification (accumulate global substitution S).
 * 2. Apply S to all inequalities.
 * 3. For each inequality τ ≤ μ, decompose structurally:
 *    - (A → B) ≤ (C → D)  →  A ≤ C and B ≤ D  (covariant decomposition)
 *    - α ≤ (C → D)        →  redex-I: substitute α := (β → γ) with fresh β, γ
 *    - (A → B) ≤ α        →  redex-I: substitute α := (β → γ) with fresh β, γ
 *    - α ≤ β              →  leave (will be resolved by other constraints)
 * 4. Repeat until no more redexes are found (fixed point).
 *
 * The solution is the accumulated substitution.
 */
object RAsupSolver {

    private var freshCounter = 0

    fun resetCounter() {
        freshCounter = 0
    }

    private fun freshVar(prefix: String = "s"): String = "${prefix}_${freshCounter++}"

    /**
     * Solve an R-ASUP instance.
     *
     * @return the solution substitution S, or null if no solution exists (type error)
     */
    fun solve(instance: RAsupInstance): Substitution? {
        var subst = Substitution.empty

        // Step 1: Solve equalities via unification
        for (eq in instance.equalities) {
            val lhs = subst.apply(eq.lhs)
            val rhs = subst.apply(eq.rhs)
            val mgu = Unification.unify(lhs, rhs) ?: return null
            subst = mgu.compose(subst)
        }

        // Step 2: Process inequalities iteratively
        // Decompose and find redex-I substitutions until fixed point
        var inequalities = instance.inequalities.map { subst.apply(it) }.toMutableList()

        var changed = true
        var maxIterations = 1000
        while (changed && maxIterations-- > 0) {
            changed = false

            val newInequalities = mutableListOf<Inequality>()
            val toRemove = mutableSetOf<Int>()

            for (i in inequalities.indices) {
                val ineq = Inequality(
                    subst.apply(inequalities[i].lhs),
                    subst.apply(inequalities[i].rhs)
                )

                val result = processInequality(ineq.lhs, ineq.rhs)
                when (result) {
                    is IneqResult.Solved -> {
                        // This inequality is already satisfied (both sides equal or both vars)
                        toRemove.add(i)
                    }
                    is IneqResult.Decomposed -> {
                        // Replace this inequality with sub-inequalities
                        toRemove.add(i)
                        newInequalities.addAll(result.subInequalities)
                        changed = true
                    }
                    is IneqResult.RedexI -> {
                        // Apply the substitution from redex-I
                        subst = result.substitution.compose(subst)
                        toRemove.add(i)
                        changed = true
                    }
                    is IneqResult.Error -> {
                        return null
                    }
                    is IneqResult.Unchanged -> {
                        // Keep as-is
                    }
                }
            }

            // Remove processed inequalities and add new ones
            inequalities = inequalities.filterIndexed { i, _ -> i !in toRemove }.toMutableList()
            inequalities.addAll(newInequalities)
        }

        return subst
    }

    /**
     * Result of processing a single inequality.
     */
    private sealed class IneqResult {
        /** Already satisfied, can be removed. */
        object Solved : IneqResult()
        /** Decomposed into sub-inequalities. */
        data class Decomposed(val subInequalities: List<Inequality>) : IneqResult()
        /** Found a redex-I, produced a substitution. */
        data class RedexI(val substitution: Substitution) : IneqResult()
        /** Type error: incompatible types. */
        object Error : IneqResult()
        /** No action possible, keep inequality. */
        object Unchanged : IneqResult()
    }

    /**
     * Process a single inequality τ ≤ μ.
     */
    private fun processInequality(lhs: Type, rhs: Type): IneqResult {
        return when {
            // Both equal — trivially satisfied
            lhs == rhs -> IneqResult.Solved

            // Both variables — leave for now
            lhs is Type.Var && rhs is Type.Var -> IneqResult.Unchanged

            // Variable on LHS, compound on RHS — redex-I
            lhs is Type.Var && rhs is Type.Arrow -> {
                // Substitute lhs variable with a fresh copy matching rhs's structure
                val freshType = freshenType(rhs)
                IneqResult.RedexI(Substitution(mapOf(lhs.name to freshType)))
            }

            // Compound on LHS, variable on RHS — redex-I (reverse)
            // The variable needs to match the compound structure
            lhs is Type.Arrow && rhs is Type.Var -> {
                val freshType = freshenType(lhs)
                IneqResult.RedexI(Substitution(mapOf(rhs.name to freshType)))
            }

            // Both arrows — decompose (covariant in semi-unification)
            lhs is Type.Arrow && rhs is Type.Arrow -> {
                IneqResult.Decomposed(
                    listOf(
                        Inequality(lhs.domain, rhs.domain),
                        Inequality(lhs.codomain, rhs.codomain)
                    )
                )
            }

            // Forall encountered — strip quantifier for first-order processing
            lhs is Type.Forall || rhs is Type.Forall -> {
                // Instantiate forall with fresh variables and retry
                val lhs2 = instantiateForall(lhs)
                val rhs2 = instantiateForall(rhs)
                processInequality(lhs2, rhs2)
            }

            else -> IneqResult.Error
        }
    }

    /**
     * Create a fresh copy of a type: replace all variables with fresh ones.
     * This is the "τ₁'" from the redex-I rule.
     */
    private fun freshenType(type: Type): Type {
        val mapping = mutableMapOf<String, Type>()
        return freshenTypeInternal(type, mapping)
    }

    private fun freshenTypeInternal(type: Type, mapping: MutableMap<String, Type>): Type =
        when (type) {
            is Type.Var -> mapping.getOrPut(type.name) { Type.Var(freshVar("f")) }
            is Type.Arrow -> Type.Arrow(
                freshenTypeInternal(type.domain, mapping),
                freshenTypeInternal(type.codomain, mapping)
            )
            is Type.Forall -> {
                val freshBound = freshVar("q")
                mapping[type.variable] = Type.Var(freshBound)
                Type.Forall(freshBound, freshenTypeInternal(type.body, mapping))
            }
        }

    /**
     * If the type is ∀α.τ, instantiate it with a fresh variable.
     * Otherwise return as-is.
     */
    private fun instantiateForall(type: Type): Type {
        if (type !is Type.Forall) return type
        val fresh = Type.Var(freshVar("inst"))
        return type.body.substitute(type.variable, fresh)
    }
}
