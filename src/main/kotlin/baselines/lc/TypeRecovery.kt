package baselines.lc

/**
 * Phase 5: Type Recovery (Section 3.4, end)
 *
 * After solving the R-ASUP instance, recover the type of the original term.
 *
 * The final type is assembled as:
 *   ∀free_vars_1. paramType₁ → ∀free_vars_2. paramType₂ → ... → bodyType
 *
 * For each λ²-bound parameter:
 *   - If user annotated: use the annotation as the parameter type
 *   - Otherwise: apply the solution to δ_param, then universally quantify
 *     over type variables that appear ONLY in that parameter's type
 *
 * For each λ³-bound parameter:
 *   - Apply the solution to ν_param (no quantification — monomorphic)
 *
 * The body type is the solution applied to the root type variable.
 */
object TypeRecovery {

    /**
     * Recover the inferred type from the R-ASUP solution.
     */
    fun recoverType(
        term: Term,
        labeledTerm: LabeledTerm,
        instance: RAsupInstance,
        solution: Substitution,
        translationInfo: TranslationInfo
    ): Type? {
        // Get the type of the whole expression
        val rootType = solution.apply(Type.Var(translationInfo.rootTypeVar))

        // Collect the outermost λ-parameters (in order) and build the arrow type
        val params = collectOuterParams(labeledTerm)

        if (params.isEmpty()) {
            // No outer abstractions — just return the root type, cleaned up
            return cleanType(rootType)
        }

        // Build the type from innermost to outermost
        var resultType = rootType

        for (param in params.reversed()) {
            val paramTypeVar = translationInfo.paramTypeVars[param.name]
                ?: translationInfo.localParamTypeVars[param.name]
                ?: continue

            val rawParamType = solution.apply(Type.Var(paramTypeVar))

            val paramType = if (param.isSpecializable) {
                // λ²-bound: check for annotation, otherwise quantify
                val annotation = translationInfo.annotations[param.name]
                if (annotation != null) {
                    annotation
                } else {
                    // Quantify over type variables that are free in this param type
                    // but not used elsewhere
                    quantifyParamType(rawParamType, resultType, params, param, translationInfo, solution)
                }
            } else {
                // λ³-bound: monomorphic, no quantification
                rawParamType
            }

            resultType = Type.Arrow(paramType, resultType)
        }

        return cleanType(resultType)
    }

    /**
     * For a λ²-bound parameter, quantify over type variables that appear in the
     * parameter type but not in the body type or other parameter types.
     */
    private fun quantifyParamType(
        paramType: Type,
        bodyType: Type,
        allParams: List<ParamInfo>,
        currentParam: ParamInfo,
        translationInfo: TranslationInfo,
        solution: Substitution
    ): Type {
        val paramFreeVars = paramType.freeVars()
        val bodyFreeVars = bodyType.freeVars()

        // Collect free vars from other parameter types
        val otherParamFreeVars = mutableSetOf<String>()
        for (other in allParams) {
            if (other.name == currentParam.name) continue
            val otherTypeVar = translationInfo.paramTypeVars[other.name]
                ?: translationInfo.localParamTypeVars[other.name]
                ?: continue
            otherParamFreeVars.addAll(solution.apply(Type.Var(otherTypeVar)).freeVars())
        }

        // Variables to quantify: in param type but not in body or other params
        val toQuantify = paramFreeVars - bodyFreeVars - otherParamFreeVars

        var result = paramType
        for (v in toQuantify.sorted()) {
            result = Type.Forall(v, result)
        }
        return result
    }

    data class ParamInfo(
        val name: String,
        val isSpecializable: Boolean
    )

    /**
     * Collect the outermost λ-parameters from the labeled term (in order).
     */
    private fun collectOuterParams(term: LabeledTerm): List<ParamInfo> {
        val params = mutableListOf<ParamInfo>()
        var current = term
        while (current is LabeledTerm.Abs) {
            params.add(
                ParamInfo(
                    name = current.param,
                    isSpecializable = current.label == AbstractionLabel.RANK2
                )
            )
            current = current.body
        }
        return params
    }

    /**
     * Clean up a type by simplifying trivial structures and
     * renaming type variables to readable names (a, b, c, ...).
     */
    private fun cleanType(type: Type): Type {
        val freeVars = type.freeVars().sorted()
        val mapping = mutableMapOf<String, Type>()
        var nameIndex = 0
        for (v in freeVars) {
            if (v.contains("_") || v.contains("$")) {
                // Internal variable — rename to a clean name
                val cleanName = generateCleanName(nameIndex++)
                mapping[v] = Type.Var(cleanName)
            }
        }
        return if (mapping.isEmpty()) type else type.substitute(mapping)
    }

    private fun generateCleanName(index: Int): String {
        val base = ('a' + (index % 26)).toString()
        val suffix = if (index >= 26) "${index / 26}" else ""
        return "$base$suffix"
    }
}

/**
 * Metadata produced during translation, needed for type recovery.
 */
data class TranslationInfo(
    /** The type variable representing the type of the entire term. */
    val rootTypeVar: String,

    /** For each λ²-bound parameter name, its type variable. */
    val paramTypeVars: Map<String, String>,

    /** For each λ³-bound parameter name, its type variable. */
    val localParamTypeVars: Map<String, String>,

    /** For each free variable name, its type variable. */
    val freeVarTypeVars: Map<String, String>,

    /** User-supplied annotations for bound variables. */
    val annotations: Map<String, Type>
)
