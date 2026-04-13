package baselines.lc

/**
 * Algorithm LC: A direct algorithm for rank-2 type inference in the
 * second-order λ-calculus.
 *
 * Reference: "A More Direct Algorithm for Type Inference in the Rank-2
 * Fragment of the Second-Order λ-Calculus" by Brad Lushman and Gordon V. Cormack (2007).
 *
 * Phases:
 *   1. λ-Labelling:        Label each abstraction as λ¹, λ², or λ³
 *   2. β-Reduction:        Eliminate all λ¹-redexes by substitution
 *   3. Translation to R-ASUP: Generate type constraints (inequalities + equalities)
 *   4. R-ASUP Solution:    Solve constraints via the redex procedure
 *   5. Type Recovery:       Reconstruct the final polymorphic type
 */
object AlgorithmLC {

    data class InferenceResult(
        val type: Type?,
        val error: String? = null,
        val debug: DebugInfo? = null
    )

    data class DebugInfo(
        val labeledTerm: LabeledTerm,
        val reducedTerm: LabeledTerm,
        val rasupInstance: RAsupInstance,
        val solution: Substitution?,
        val translationInfo: TranslationInfo
    )

    /**
     * Infer the type of a term.
     *
     * @param term the input term
     * @param typeEnv type environment mapping free variable names to their known types
     * @param debug if true, populate debug info in the result
     * @return the inference result
     */
    fun infer(
        term: Term,
        typeEnv: Map<String, Type> = emptyMap(),
        debug: Boolean = false
    ): InferenceResult {
        return try {
            // Phase 1: λ-Labelling
            val labeled = LambdaLabelling.label(term)

            // Phase 2: β-Reduction
            val reduced = BetaReduction.reduce(labeled)

            // Phase 3: Translation to R-ASUP
            val (instance, translationInfo) = TranslateToRAsup.translate(reduced, typeEnv)

            // Phase 4: Solve R-ASUP
            val solution = RAsupSolver.solve(instance)
                ?: return InferenceResult(
                    type = null,
                    error = "Type error: R-ASUP instance has no solution",
                    debug = if (debug) DebugInfo(labeled, reduced, instance, null, translationInfo) else null
                )

            // Phase 5: Type Recovery
            val inferredType = TypeRecovery.recoverType(
                term, reduced, instance, solution, translationInfo
            )

            InferenceResult(
                type = inferredType,
                error = if (inferredType == null) "Type recovery failed" else null,
                debug = if (debug) DebugInfo(labeled, reduced, instance, solution, translationInfo) else null
            )
        } catch (e: Exception) {
            InferenceResult(type = null, error = "Inference failed: ${e.message}")
        }
    }
}
