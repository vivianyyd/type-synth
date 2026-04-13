package baselines.lc

/**
 * Terms of the second-order λ-calculus (System F, rank-2 fragment).
 *
 * The input language:
 *   M ::= x | λx.M | M N | λx:σ.M | ΛX.M
 *
 * We also support let-expressions as sugar: let x = M in N ≡ (λx.N) M
 *
 * After λ-labelling, abstractions carry a label (1, 2, or 3).
 */
sealed class Term {
    /** Variable reference. */
    data class Var(val name: String) : Term() {
        override fun toString(): String = name
    }

    /**
     * λ-abstraction: λx.body
     * [annotation] is an optional user-supplied type annotation for x.
     */
    data class Abs(val param: String, val body: Term, val annotation: Type? = null) : Term() {
        override fun toString(): String {
            val ann = if (annotation != null) ":$annotation" else ""
            return "(λ$param$ann. $body)"
        }
    }

    /** Application: function applied to argument. */
    data class App(val func: Term, val arg: Term) : Term() {
        override fun toString(): String = "($func $arg)"
    }

    /**
     * Type abstraction: Λα.body (polymorphic generalization).
     * Only relevant in the full System F; for rank-2 inference, these
     * may appear in the input but the algorithm reasons about them.
     */
    data class TypeAbs(val typeVar: String, val body: Term) : Term() {
        override fun toString(): String = "(Λ$typeVar. $body)"
    }

    /**
     * Type application: M [σ] (instantiation).
     */
    data class TypeApp(val term: Term, val typeArg: Type) : Term() {
        override fun toString(): String = "($term [$typeArg])"
    }

    // ---- Helpers ----

    /** All free term-level variables. */
    fun freeVars(): Set<String> = when (this) {
        is Var -> setOf(name)
        is Abs -> body.freeVars() - param
        is App -> func.freeVars() + arg.freeVars()
        is TypeAbs -> body.freeVars()
        is TypeApp -> term.freeVars()
    }
}

/**
 * A labeled term, produced by the λ-labelling phase (Section 3.1).
 *
 * After labelling, every abstraction carries a label indicating
 * whether it is:
 *   1 (λ¹): argument has been supplied (not polymorphic)
 *   2 (λ²): argument not supplied, but appears as non-proper subexpression (polymorphic)
 *   3 (λ³): any other abstraction
 *
 * β-reduction and translation to R-ASUP operate on labeled terms.
 */
sealed class LabeledTerm {
    data class Var(val name: String) : LabeledTerm()

    data class Abs(
        val param: String,
        val body: LabeledTerm,
        val label: AbstractionLabel,
        val annotation: Type? = null
    ) : LabeledTerm()

    data class App(val func: LabeledTerm, val arg: LabeledTerm) : LabeledTerm()

    /** After β-reduction, type abstractions and type applications are erased. */
}

/**
 * Labels for λ-abstractions (Section 3.1).
 *
 * - RANK1: λ¹ — a polymorphic abstraction whose argument has been supplied
 * - RANK2: λ² — a polymorphic abstraction whose argument has NOT been supplied,
 *               but it appears as a (not necessarily proper) subexpression of some function argument
 * - RANK3: λ³ — any other abstraction
 */
enum class AbstractionLabel {
    RANK1,
    RANK2,
    RANK3
}
