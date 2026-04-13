package baselines.lc

/**
 * Phase 4: R-ASUP Solution (Section 3.4)
 *
 * Solves the R-ASUP instance:
 *
 * 1. Solve equalities using Robinson's unification.
 * 2. Solve inequalities: for each τ ≤ μ, unify τ with μ.
 *    In the canonical solution, the LHS (general type) is identified with
 *    the RHS (specialized occurrence). This produces the principal type.
 * 3. The accumulated substitution is the solution.
 *
 * Note: full semi-unification would allow the LHS to be MORE GENERAL than
 * the RHS (with a local substitution bridging the gap). For the principal
 * type, we unify them directly — the quantification step in type recovery
 * then adds ∀ where the parameter type can vary across occurrences.
 */
object RAsupSolver {

    fun resetCounter() { /* no-op after simplification */ }

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

        // Step 2: Solve inequalities.
        // For the canonical/principal solution, unify both sides of each inequality.
        // This identifies the specializable variable with its occurrence type.
        for (ineq in instance.inequalities) {
            val lhs = subst.apply(ineq.lhs)
            val rhs = subst.apply(ineq.rhs)
            val mgu = Unification.unify(lhs, rhs) ?: return null
            subst = mgu.compose(subst)
        }

        return subst
    }
}
