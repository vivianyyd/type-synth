package baselines.lc

/**
 * Phase 1: λ-Labelling (Section 3.1)
 *
 * Labels each abstraction as λ¹, λ², or λ³:
 *   - λ¹: argument has been supplied (directly applied)
 *   - λ²: argument not supplied, appears inside an argument subtree
 *   - λ³: any other abstraction (standalone, monomorphic without annotation)
 *
 * Formula: lbl(M N, X, S) = lbl(M, X, S)  lbl(N, X, S ∪ act(N))
 *
 * When descending into an argument N, S is augmented with act(N) so that
 * any unmatched λ inside the argument gets λ². This handles the common
 * case: g (λx. x) where λx needs to be polymorphic if g expects ∀a.a→a.
 *
 * For standalone functions like λf. pair (f 1) (f true), f needs a user
 * annotation to be treated polymorphically (this matches the paper's
 * algorithm which requires annotations for top-level rank-2 parameters).
 */
object LambdaLabelling {

    fun label(term: Term): LabeledTerm {
        val active = activeVars(term)
        return lbl(term, active, emptySet())
    }

    /**
     * Compute active variables: free variable references + unmatched binders.
     */
    internal fun activeVars(term: Term): Set<String> = when (term) {
        is Term.Var -> setOf(term.name)
        is Term.Abs -> setOf(term.param) + activeVars(term.body)
        is Term.App -> {
            val funcAct = activeVars(term.func)
            val argAct = activeVars(term.arg)
            if (term.func is Term.Abs) {
                (funcAct - term.func.param) + argAct
            } else {
                funcAct + argAct
            }
        }
        is Term.TypeAbs -> activeVars(term.body)
        is Term.TypeApp -> activeVars(term.term)
    }

    /**
     * Label the term. S is augmented when entering argument positions.
     */
    internal fun lbl(term: Term, active: Set<String>, s: Set<String>): LabeledTerm = when (term) {
        is Term.Var -> LabeledTerm.Var(term.name)

        is Term.Abs -> {
            val label = when {
                term.param !in active -> AbstractionLabel.RANK1
                term.param in s -> AbstractionLabel.RANK2
                else -> AbstractionLabel.RANK3
            }
            LabeledTerm.Abs(term.param, lbl(term.body, active, s), label, term.annotation)
        }

        is Term.App -> {
            val argAct = activeVars(term.arg)
            LabeledTerm.App(
                lbl(term.func, active, s),
                lbl(term.arg, active, s + argAct)
            )
        }

        is Term.TypeAbs -> lbl(term.body, active, s)
        is Term.TypeApp -> lbl(term.term, active, s)
    }
}
