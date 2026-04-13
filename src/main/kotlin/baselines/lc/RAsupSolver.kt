package baselines.lc

/**
 * Phase 4: R-ASUP Solution (Section 3.4)
 *
 * Implements the paper's redex procedure:
 *
 * 1. Solve equalities via Robinson's unification (standard unification,
 *    accumulate global substitution S).
 *
 * 2. Repeatedly find and apply redexes in inequalities:
 *
 *    - redex-I: For τ ≤ μ where at corresponding positions α is a variable
 *      (in τ) and τ₁ is a COMPOUND type (in μ), substitute α := τ₁' where
 *      τ₁' is τ₁ with all variables replaced by fresh ones.
 *
 *    - Arrow decomposition: (A → B) ≤ (C → D) → A ≤ C and B ≤ D.
 *
 * 3. Final pass: for remaining var ≤ var inequalities, bind the internal
 *    (generated) variable to the other to produce the canonical solution.
 *
 * The freshening in redex-I is critical: it's what enables rank-2 polymorphism.
 * When a specializable variable meets a compound type, we don't unify them
 * directly — we give the variable fresh internal structure so that different
 * inequalities can specialize it differently.
 */
object RAsupSolver {

    private var freshCounter = 0

    fun resetCounter() { freshCounter = 0 }

    private fun freshVar(prefix: String = "s"): String = "${prefix}_${freshCounter++}"

    /**
     * Solve an R-ASUP instance.
     */
    fun solve(instance: RAsupInstance): Substitution? {
        var subst = Substitution.empty

        // Step 1: Solve equalities via unification
        for (eq in instance.equalities) {
            val mgu = Unification.unify(subst.apply(eq.lhs), subst.apply(eq.rhs)) ?: return null
            subst = mgu.compose(subst)
        }

        // Step 2: Iteratively apply redex-I and decomposition
        var inequalities = instance.inequalities.toMutableList()
        var maxIterations = 1000
        while (maxIterations-- > 0) {
            var changed = false
            val newInequalities = mutableListOf<Inequality>()

            for (ineq in inequalities) {
                val lhs = subst.apply(ineq.lhs)
                val rhs = subst.apply(ineq.rhs)
                when (val result = processInequality(lhs, rhs)) {
                    is IneqResult.Trivial -> {
                        // Already satisfied (lhs == rhs after subst), drop
                        changed = true
                    }
                    is IneqResult.Decomposed -> {
                        newInequalities.addAll(result.subInequalities)
                        changed = true
                    }
                    is IneqResult.RedexI -> {
                        subst = result.substitution.compose(subst)
                        // Re-queue the current inequality for further processing
                        newInequalities.add(ineq)
                        changed = true
                    }
                    is IneqResult.Keep -> {
                        newInequalities.add(Inequality(lhs, rhs))
                    }
                    is IneqResult.Error -> return null
                }
            }

            inequalities = newInequalities
            if (!changed) break
        }

        // Step 3: For remaining var ≤ var inequalities, bind internal vars
        // to produce the canonical solution.
        for (ineq in inequalities) {
            val lhs = subst.apply(ineq.lhs)
            val rhs = subst.apply(ineq.rhs)
            if (lhs is Type.Var && rhs is Type.Var && lhs != rhs) {
                val mgu = Unification.unify(lhs, rhs)
                if (mgu != null) subst = mgu.compose(subst)
            }
        }

        return subst
    }

    private sealed class IneqResult {
        /** τ = μ after subst — trivially satisfied, drop. */
        object Trivial : IneqResult()
        /** Decomposed into sub-inequalities. */
        data class Decomposed(val subInequalities: List<Inequality>) : IneqResult()
        /** Redex-I applied: variable on LHS substituted with fresh copy of RHS structure. */
        data class RedexI(val substitution: Substitution) : IneqResult()
        /** Keep as-is (e.g., both sides are variables — wait for post-processing). */
        object Keep : IneqResult()
        /** Type error. */
        object Error : IneqResult()
    }

    /**
     * Process one inequality. See class docs for redex rules.
     */
    private fun processInequality(lhs: Type, rhs: Type): IneqResult = when {
        lhs == rhs -> IneqResult.Trivial

        // Both variables: keep for post-processing
        lhs is Type.Var && rhs is Type.Var -> IneqResult.Keep

        // Redex-I: variable on LHS, compound on RHS
        // Substitute α := fresh copy of RHS structure.
        // Occurs check: if α appears in the RHS, this is a cyclic type → error.
        lhs is Type.Var && rhs is Type.Arrow -> {
            if (Unification.occursIn(lhs.name, rhs)) {
                IneqResult.Error
            } else {
                val freshStructure = freshStructureLike(rhs)
                IneqResult.RedexI(Substitution(mapOf(lhs.name to freshStructure)))
            }
        }

        // Compound on LHS, variable on RHS: unify (the variable gets the LHS).
        // Occurs check prevents cyclic types.
        lhs is Type.Arrow && rhs is Type.Var -> {
            if (Unification.occursIn(rhs.name, lhs)) {
                IneqResult.Error
            } else {
                IneqResult.RedexI(Substitution(mapOf(rhs.name to lhs)))
            }
        }

        // Both arrows: decompose
        lhs is Type.Arrow && rhs is Type.Arrow -> {
            IneqResult.Decomposed(listOf(
                Inequality(lhs.domain, rhs.domain),
                Inequality(lhs.codomain, rhs.codomain)
            ))
        }

        // Handle ∀ by instantiation (shouldn't normally arise during solving)
        lhs is Type.Forall -> processInequality(instantiateForall(lhs), rhs)
        rhs is Type.Forall -> processInequality(lhs, instantiateForall(rhs))

        else -> IneqResult.Error
    }

    /**
     * Build a type with the same ARROW STRUCTURE as [template] but with
     * FRESH variables at every position. This is the τ₁' from the paper's redex-I.
     * This enables independent specialization for different inequalities.
     */
    private fun freshStructureLike(template: Type): Type = when (template) {
        is Type.Var -> Type.Var(freshVar("s"))
        is Type.Arrow -> Type.Arrow(
            freshStructureLike(template.domain),
            freshStructureLike(template.codomain)
        )
        is Type.Forall -> freshStructureLike(template.body)
    }

    private fun instantiateForall(type: Type): Type =
        if (type is Type.Forall) type.body.substitute(type.variable, Type.Var(freshVar("inst")))
        else type
}
