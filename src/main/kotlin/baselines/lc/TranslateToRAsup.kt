package baselines.lc

/**
 * Phase 3: Translation to R-ASUP (Section 3.3)
 *
 * Translates a β-reduced labeled term into an R-ASUP instance: a set of
 * type inequalities and equalities over type variables.
 *
 * Variable scheme (one type variable per term variable — the LC optimization):
 *   - Each λ²-bound variable x: δ_x (specializable — can be used at different types)
 *   - Each λ³-bound variable y: ν_y (non-specializable — same type at all occurrences)
 *   - Each free variable w: Δ_w (non-specializable)
 *   - Each subexpression E: d_E (derived type variable for the expression's type)
 *
 * Constraints generated:
 *   - Application M N:  d_M = d_N → d_{MN}           (function typing rule)
 *   - λ²x.M:           d_{λx.M} = δ_x → d_M          (function type)
 *   - λ³x.M:           d_{λx.M} = ν_x → d_M           (function type)
 *   - Occurrence of λ²-bound x:  δ_x ≤ d_{occurrence}  (semi-unification: specializable)
 *   - Occurrence of λ³-bound y:  ν_y = d_{occurrence}   (unification: non-specializable)
 *   - Occurrence of free var w:   Δ_w = d_{occurrence}   (unification)
 *   - User annotation on x:      δ_x = annotated_type   (or ν_x for λ³)
 *   - Type env for free var w:    Δ_w = env_type
 */
object TranslateToRAsup {

    /**
     * Translate a β-reduced labeled term into an R-ASUP instance.
     *
     * @return pair of (R-ASUP instance, translation metadata for type recovery)
     */
    fun translate(
        term: LabeledTerm,
        typeEnv: Map<String, Type> = emptyMap()
    ): Pair<RAsupInstance, TranslationInfo> {
        val state = TranslationState()

        // Walk the term to discover all bound and free variables first
        discoverVariables(term, state, mutableSetOf())

        // Set up type environment constraints for free variables
        for ((varName, type) in typeEnv) {
            val typeVarName = state.freeVarTypes[varName] ?: continue
            state.equalities.add(Equality(Type.Var(typeVarName), type))
        }

        // Set up annotation constraints
        for ((paramName, annotation) in state.annotations) {
            val typeVarName = state.boundVarTypes[paramName] ?: continue
            state.equalities.add(Equality(Type.Var(typeVarName), annotation))
        }

        // Translate the term, producing constraints
        val rootTypeVar = translateExpr(term, state)

        val info = TranslationInfo(
            rootTypeVar = rootTypeVar,
            paramTypeVars = state.rank2Params.associateWith { state.boundVarTypes[it]!! },
            localParamTypeVars = state.rank3Params.associateWith { state.boundVarTypes[it]!! },
            freeVarTypeVars = state.freeVarTypes.toMap(),
            annotations = state.annotations.toMap()
        )

        return state.toInstance() to info
    }

    /**
     * Walk the term to discover all variables and create type variables for them.
     */
    private fun discoverVariables(
        term: LabeledTerm,
        state: TranslationState,
        boundScope: MutableSet<String>
    ) {
        when (term) {
            is LabeledTerm.Var -> {
                if (term.name !in boundScope && term.name !in state.freeVarTypes) {
                    // Free variable: create a non-specializable type variable
                    val tv = state.freshTypeVar("Δ_${term.name}")
                    state.freeVarTypes[term.name] = tv
                    state.nonSpecializableVars.add(tv)
                }
            }
            is LabeledTerm.Abs -> {
                if (term.param !in state.boundVarTypes) {
                    val prefix = if (term.label == AbstractionLabel.RANK2) "δ" else "ν"
                    val tv = state.freshTypeVar("${prefix}_${term.param}")
                    state.boundVarTypes[term.param] = tv
                    if (term.label == AbstractionLabel.RANK2) {
                        state.specializableVars.add(tv)
                        state.rank2Params.add(term.param)
                    } else {
                        state.nonSpecializableVars.add(tv)
                        state.rank3Params.add(term.param)
                    }
                    if (term.annotation != null) {
                        state.annotations[term.param] = term.annotation
                    }
                }
                boundScope.add(term.param)
                discoverVariables(term.body, state, boundScope)
                boundScope.remove(term.param)
            }
            is LabeledTerm.App -> {
                discoverVariables(term.func, state, boundScope)
                discoverVariables(term.arg, state, boundScope)
            }
        }
    }

    /**
     * Recursively translate a subexpression, returning the type variable
     * representing the type of this subexpression.
     */
    internal fun translateExpr(
        term: LabeledTerm,
        state: TranslationState
    ): String = when (term) {
        is LabeledTerm.Var -> {
            // Create a fresh derived type variable for this occurrence
            val dOcc = state.freshTypeVar("d_${term.name}")

            val boundTypeVar = state.boundVarTypes[term.name]
            val freeTypeVar = state.freeVarTypes[term.name]

            when {
                boundTypeVar != null && boundTypeVar in state.specializableVars -> {
                    // λ²-bound: inequality δ_x ≤ d_occurrence (specializable)
                    state.inequalities.add(
                        Inequality(Type.Var(boundTypeVar), Type.Var(dOcc))
                    )
                }
                boundTypeVar != null -> {
                    // λ³-bound: equality ν_x = d_occurrence
                    state.equalities.add(
                        Equality(Type.Var(boundTypeVar), Type.Var(dOcc))
                    )
                }
                freeTypeVar != null -> {
                    // Free variable: equality Δ_w = d_occurrence
                    state.equalities.add(
                        Equality(Type.Var(freeTypeVar), Type.Var(dOcc))
                    )
                }
                else -> {
                    // Unknown variable — treat as free with fresh type
                    val tv = state.freshTypeVar("Δ_${term.name}")
                    state.freeVarTypes[term.name] = tv
                    state.nonSpecializableVars.add(tv)
                    state.equalities.add(
                        Equality(Type.Var(tv), Type.Var(dOcc))
                    )
                }
            }

            dOcc
        }

        is LabeledTerm.Abs -> {
            // Translate the body
            val bodyTypeVar = translateExpr(term.body, state)

            // The type of this abstraction: paramType → bodyType
            val paramTypeVar = state.boundVarTypes[term.param]
                ?: error("Parameter ${term.param} not found in bound variables")

            val absTypeVar = state.freshTypeVar("d_abs")
            state.equalities.add(
                Equality(
                    Type.Var(absTypeVar),
                    Type.Arrow(Type.Var(paramTypeVar), Type.Var(bodyTypeVar))
                )
            )

            absTypeVar
        }

        is LabeledTerm.App -> {
            // Translate function and argument
            val funcTypeVar = translateExpr(term.func, state)
            val argTypeVar = translateExpr(term.arg, state)

            // The function type must be: argType → resultType
            val resultTypeVar = state.freshTypeVar("d_app")
            state.equalities.add(
                Equality(
                    Type.Var(funcTypeVar),
                    Type.Arrow(Type.Var(argTypeVar), Type.Var(resultTypeVar))
                )
            )

            resultTypeVar
        }
    }

    /**
     * State maintained during translation.
     */
    internal class TranslationState {
        val inequalities = mutableListOf<Inequality>()
        val equalities = mutableListOf<Equality>()
        val specializableVars = mutableSetOf<String>()
        val nonSpecializableVars = mutableSetOf<String>()

        /** Maps bound variable name → its type variable name. */
        val boundVarTypes = mutableMapOf<String, String>()

        /** Maps free variable name → its type variable name. */
        val freeVarTypes = mutableMapOf<String, String>()

        /** User annotations for bound variables. */
        val annotations = mutableMapOf<String, Type>()

        /** Names of λ²-bound parameters. */
        val rank2Params = mutableListOf<String>()

        /** Names of λ³-bound parameters. */
        val rank3Params = mutableListOf<String>()

        private var freshCounter = 0

        fun freshTypeVar(prefix: String = "t"): String = "${prefix}_${freshCounter++}"

        fun toInstance(): RAsupInstance = RAsupInstance(
            inequalities = inequalities.toList(),
            equalities = equalities.toList(),
            specializableVars = specializableVars.toSet(),
            nonSpecializableVars = nonSpecializableVars.toSet()
        )
    }
}
