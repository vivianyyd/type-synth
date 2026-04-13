package baselines.lc

/**
 * Variable Reduction (Section 5)
 *
 * In Algorithm KW, each variable in a θ-normal term gets n+1 specializable
 * type variables. Algorithm LC already uses only ONE type variable per
 * bound variable, so this optimization is built into the translation.
 *
 * This module is a no-op for Algorithm LC — the optimization is inherent
 * in the TranslateToRAsup phase. It exists for documentation and potential
 * use if a KW-style translation is added later.
 */
object VariableReduction {

    /**
     * For LC: identity — the optimization is already built in.
     * For a hypothetical KW translation, this would collapse variable chains.
     */
    fun reduce(instance: RAsupInstance): RAsupInstance = instance
}
