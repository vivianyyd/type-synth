package baselines.lc

/**
 * Phase 5: Type Recovery (Section 3.4, end)
 *
 * After solving the R-ASUP instance, recover the type of the original term.
 *
 * The root type variable already represents the full type of the term (including
 * all arrow structure from abstractions). Type recovery:
 *   1. Applies the solution substitution to the root type variable
 *   2. Walks the arrow chain matching outer λ-parameters
 *   3. For λ²-bound parameters, adds ∀ quantifiers over type variables
 *      that appear only in that parameter's domain
 *   4. Cleans up internal variable names to readable ones (a, b, c, ...)
 */
object TypeRecovery {

    fun recoverType(
        term: Term,
        labeledTerm: LabeledTerm,
        instance: RAsupInstance,
        solution: Substitution,
        translationInfo: TranslationInfo
    ): Type? {
        val rootType = solution.apply(Type.Var(translationInfo.rootTypeVar))
        val params = collectOuterParams(labeledTerm)

        if (params.isEmpty()) {
            return cleanType(rootType)
        }

        // The rootType already has shape: paramType₁ → paramType₂ → ... → bodyType
        // We walk the arrow chain and add ∀ quantifiers for λ² parameters.
        val quantified = addQuantifiers(rootType, params, 0)
        return cleanType(quantified)
    }

    /**
     * Walk the arrow chain of [type], matching each arrow's domain to the
     * corresponding parameter. For λ² parameters, quantify over type variables
     * that appear ONLY in that parameter's domain (not in any other param type
     * or in the body).
     */
    private fun addQuantifiers(type: Type, params: List<ParamInfo>, index: Int): Type {
        if (index >= params.size) return type
        if (type !is Type.Arrow) return type

        val param = params[index]

        // Collect free vars from ALL other parts of the type:
        // - previous param types (their domains, via the arrow chain above)
        // - later params' domains and the final body
        val otherFreeVars = freeVarsOutsidePosition(type, index, params.size)

        val domain = if (param.isSpecializable) {
            // Quantify only variables that appear in THIS domain but NOWHERE else
            val domainFreeVars = type.domain.freeVars()
            val toQuantify = domainFreeVars - otherFreeVars

            var quantifiedDomain = type.domain
            for (v in toQuantify.sorted()) {
                quantifiedDomain = Type.Forall(v, quantifiedDomain)
            }
            quantifiedDomain
        } else {
            type.domain
        }

        val restType = addQuantifiers(type.codomain, params, index + 1)
        return Type.Arrow(domain, restType)
    }

    /**
     * Collect free variables from all domain positions EXCEPT the one at [targetIndex],
     * plus the final body type. Used to determine what can be safely quantified.
     */
    private fun freeVarsOutsidePosition(
        type: Type, targetIndex: Int, totalParams: Int
    ): Set<String> {
        val result = mutableSetOf<String>()
        var current = type
        var i = 0
        while (current is Type.Arrow && i < totalParams) {
            if (i != targetIndex) {
                result.addAll(current.domain.freeVars())
            }
            current = current.codomain
            i++
        }
        // Add free vars from the body (whatever's left after walking past all params)
        result.addAll(current.freeVars())
        return result
    }

    data class ParamInfo(
        val name: String,
        val isSpecializable: Boolean
    )

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
     * Clean up a type by renaming internal type variables to readable names.
     */
    private fun cleanType(type: Type): Type {
        val freeVars = type.freeVars().sorted()
        val mapping = mutableMapOf<String, Type>()
        var nameIndex = 0
        for (v in freeVars) {
            if (v.contains("_") || v.contains("$")) {
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
    val rootTypeVar: String,
    val paramTypeVars: Map<String, String>,
    val localParamTypeVars: Map<String, String>,
    val freeVarTypeVars: Map<String, String>,
    val annotations: Map<String, Type>
)
