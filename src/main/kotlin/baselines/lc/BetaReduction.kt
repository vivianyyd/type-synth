package baselines.lc

/**
 * Phase 2: β-Reduction (Section 3.2)
 *
 * Eliminates all λ¹-redexes by substitution. A λ¹-redex is an application
 * (λ¹x.M) N — since x was matched with an argument, we substitute M[x := N].
 *
 * After β-reduction, only λ² and λ³ abstractions remain.
 *
 * During substitution, bound variables in the substituted term are alpha-renamed
 * to fresh names to avoid capture and ensure each bound variable name is unique.
 */
object BetaReduction {

    private var freshCounter = 0

    fun resetCounter() {
        freshCounter = 0
    }

    private fun freshName(base: String): String = "${base}_r${freshCounter++}"

    /**
     * Perform β-reduction: repeatedly reduce λ¹-redexes until none remain.
     */
    fun reduce(term: LabeledTerm): LabeledTerm {
        var current = term
        var maxIterations = 1000
        while (hasRedex(current) && maxIterations-- > 0) {
            current = reduceOnce(current)
        }
        return current
    }

    /**
     * Perform one step of β-reduction (reduce the leftmost-outermost λ¹-redex).
     */
    internal fun reduceOnce(term: LabeledTerm): LabeledTerm = when (term) {
        is LabeledTerm.Var -> term

        is LabeledTerm.Abs -> LabeledTerm.Abs(
            term.param, reduceOnce(term.body), term.label, term.annotation
        )

        is LabeledTerm.App -> {
            val func = term.func
            if (func is LabeledTerm.Abs && func.label == AbstractionLabel.RANK1) {
                // λ¹-redex: (λ¹x.M) N → M[x := N]
                // Each occurrence of the parameter in the body gets a FRESH
                // alpha-renamed copy of the argument, so that duplicated
                // polymorphic arguments get independent type variables.
                substituteWithFreshCopies(func.body, func.param, term.arg)
            } else {
                // Not a λ¹-redex at this level; try reducing inside
                LabeledTerm.App(reduceOnce(term.func), reduceOnce(term.arg))
            }
        }
    }

    /**
     * Alpha-rename all bound variables in [term] to fresh names.
     * This prevents variable capture during substitution.
     */
    internal fun alphaRename(term: LabeledTerm): LabeledTerm = when (term) {
        is LabeledTerm.Var -> term
        is LabeledTerm.Abs -> {
            val newName = freshName(term.param)
            val renamedBody = substitute(term.body, term.param, LabeledTerm.Var(newName))
            LabeledTerm.Abs(newName, alphaRename(renamedBody), term.label, term.annotation)
        }
        is LabeledTerm.App -> LabeledTerm.App(alphaRename(term.func), alphaRename(term.arg))
    }

    /**
     * Substitute [param] in [body], creating a FRESH alpha-renamed copy of [template]
     * at each occurrence. This ensures that when a polymorphic argument is duplicated
     * (e.g., f used twice in (λf. f f)), each copy gets independent bound variable names.
     */
    internal fun substituteWithFreshCopies(
        body: LabeledTerm, param: String, template: LabeledTerm
    ): LabeledTerm = when (body) {
        is LabeledTerm.Var ->
            if (body.name == param) alphaRename(template) else body
        is LabeledTerm.Abs -> {
            if (body.param == param) body
            else LabeledTerm.Abs(
                body.param,
                substituteWithFreshCopies(body.body, param, template),
                body.label, body.annotation
            )
        }
        is LabeledTerm.App -> LabeledTerm.App(
            substituteWithFreshCopies(body.func, param, template),
            substituteWithFreshCopies(body.arg, param, template)
        )
    }

    /**
     * Substitute [param] with [arg] in [body].
     */
    internal fun substitute(body: LabeledTerm, param: String, arg: LabeledTerm): LabeledTerm =
        when (body) {
            is LabeledTerm.Var ->
                if (body.name == param) arg else body

            is LabeledTerm.Abs -> {
                if (body.param == param) {
                    // Shadowed — don't substitute inside
                    body
                } else {
                    LabeledTerm.Abs(
                        body.param,
                        substitute(body.body, param, arg),
                        body.label,
                        body.annotation
                    )
                }
            }

            is LabeledTerm.App -> LabeledTerm.App(
                substitute(body.func, param, arg),
                substitute(body.arg, param, arg)
            )
        }

    /**
     * Check if the term contains any λ¹-redex.
     */
    internal fun hasRedex(term: LabeledTerm): Boolean = when (term) {
        is LabeledTerm.Var -> false
        is LabeledTerm.Abs -> hasRedex(term.body)
        is LabeledTerm.App -> {
            val func = term.func
            (func is LabeledTerm.Abs && func.label == AbstractionLabel.RANK1) ||
                hasRedex(term.func) || hasRedex(term.arg)
        }
    }
}
