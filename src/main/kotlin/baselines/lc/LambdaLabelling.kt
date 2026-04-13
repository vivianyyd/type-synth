package baselines.lc

/**
 * Phase 1: λ-Labelling (Section 3.1)
 *
 * Labels each abstraction in the term as λ¹, λ², or λ³:
 *   - λ¹: argument has been supplied (directly applied)
 *   - λ²: argument not supplied, but appears as a subexpression of a function argument
 *   - λ³: any other abstraction (monomorphic)
 *
 * The labelling uses two precomputed sets:
 *   X = act(M): the set of "active" variables (free vars + unmatched bound vars)
 *   S: accumulated set — when entering an argument N, S is augmented with act(N),
 *      so that any unmatched λ inside the argument gets λ².
 *
 * Formula: lbl(M N, X, S) = lbl(M, X, S)  lbl(N, X, S ∪ act(N))
 */
object LambdaLabelling {

    /**
     * Label all abstractions in [term].
     */
    fun label(term: Term): LabeledTerm {
        val active = activeVars(term)
        return lbl(term, active, emptySet())
    }

    /**
     * Compute the set of "active" variables in a term.
     *
     * act(x)     = {x}                          (variable reference)
     * act(λx.M)  = {x} ∪ act(M)                 (x is an unmatched binder)
     * act(M N)   = (act(M) - {p}) ∪ act(N)      (if M = λp.M', p is matched)
     * act(M N)   = act(M) ∪ act(N)              (if M is not a λ)
     * act(Λα.M)  = act(M)
     * act(M[σ])  = act(M)
     */
    internal fun activeVars(term: Term): Set<String> = when (term) {
        is Term.Var -> setOf(term.name)
        is Term.Abs -> setOf(term.param) + activeVars(term.body)
        is Term.App -> {
            val funcAct = activeVars(term.func)
            val argAct = activeVars(term.arg)
            if (term.func is Term.Abs) {
                // The function's parameter is matched with the argument
                (funcAct - term.func.param) + argAct
            } else {
                funcAct + argAct
            }
        }
        is Term.TypeAbs -> activeVars(term.body)
        is Term.TypeApp -> activeVars(term.term)
    }

    /**
     * lbl(term, X, S): label the term given active set X and accumulated argument-actives S.
     *
     * For application M N:
     *   - Function M gets S unchanged
     *   - Argument N gets S ∪ act(N)  (self-augmentation ensures unmatched λs in args get λ²)
     *
     * For λx.M:
     *   - label 1 if x ∉ X  (matched with argument)
     *   - label 2 if x ∈ X and x ∈ S  (unmatched, inside an argument)
     *   - label 3 if x ∈ X and x ∉ S  (unmatched, not inside an argument)
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
