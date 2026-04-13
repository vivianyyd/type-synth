package baselines.lc

/**
 * Phase 1: λ-Labelling (Section 3.1)
 *
 * Labels each abstraction as λ¹, λ², or λ³:
 *   - λ¹: argument has been supplied (directly applied)
 *   - λ²: polymorphic — argument not supplied, parameter needs polymorphic type
 *   - λ³: any other abstraction (monomorphic)
 *
 * The paper's formula propagates S to identify λs INSIDE arguments.
 * We also extend: a parameter that appears MULTIPLE TIMES in its body
 * may need polymorphism (each occurrence could be used at a different type),
 * so we conservatively mark such abstractions λ². This is safe because the
 * semi-unification solver collapses polymorphism to monomorphism when possible.
 */
object LambdaLabelling {

    fun label(term: Term): LabeledTerm {
        val active = activeVars(term)
        val multiUse = multipleUseVars(term)
        return lbl(term, active, multiUse)
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
     * Identify bound variables whose parameter is USED 2+ times in the body.
     * Such variables may need polymorphic typing (since different occurrences
     * could be used at different types).
     */
    internal fun multipleUseVars(term: Term): Set<String> {
        val result = mutableSetOf<String>()
        findMultiUseAbs(term, result)
        return result
    }

    private fun findMultiUseAbs(term: Term, result: MutableSet<String>) {
        when (term) {
            is Term.Var -> { }
            is Term.Abs -> {
                val useCount = countOccurrences(term.body, term.param)
                if (useCount >= 2) result.add(term.param)
                findMultiUseAbs(term.body, result)
            }
            is Term.App -> {
                findMultiUseAbs(term.func, result)
                findMultiUseAbs(term.arg, result)
            }
            is Term.TypeAbs -> findMultiUseAbs(term.body, result)
            is Term.TypeApp -> findMultiUseAbs(term.term, result)
        }
    }

    private fun countOccurrences(term: Term, name: String): Int = when (term) {
        is Term.Var -> if (term.name == name) 1 else 0
        is Term.Abs -> if (term.param == name) 0 else countOccurrences(term.body, name)
        is Term.App -> countOccurrences(term.func, name) + countOccurrences(term.arg, name)
        is Term.TypeAbs -> countOccurrences(term.body, name)
        is Term.TypeApp -> countOccurrences(term.term, name)
    }

    /**
     * Label the term. S (eligibility for λ²) is:
     *   - Initially: the set of multi-use bound variables (global)
     *   - When entering an argument N: augmented with act(N) (per paper)
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
