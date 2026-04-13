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
     * corresponding parameter. For λ² parameters, quantify the domain.
     */
    private fun addQuantifiers(type: Type, params: List<ParamInfo>, index: Int): Type {
        if (index >= params.size) return type
        if (type !is Type.Arrow) return type

        val param = params[index]
        val restType = addQuantifiers(type.codomain, params, index + 1)

        val domain = if (param.isSpecializable) {
            // Quantify over type variables in the domain that don't appear in the codomain
            val domainFreeVars = type.domain.freeVars()
            val codomainFreeVars = restType.freeVars()
            val toQuantify = domainFreeVars - codomainFreeVars

            var quantifiedDomain = type.domain
            for (v in toQuantify.sorted()) {
                quantifiedDomain = Type.Forall(v, quantifiedDomain)
            }
            quantifiedDomain
        } else {
            type.domain
        }

        return Type.Arrow(domain, restType)
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
