package baselines.lc

/**
 * Types in the rank-2 fragment of the second-order λ-calculus.
 *
 * τ (monotypes): type variables α, or τ₁ → τ₂
 * σ (polytypes): τ, or ∀α.σ  (but quantifiers only appear on left of arrow at rank ≤ 2)
 *
 * For SUP/ASUP, we work with "specializable" type variables (can be replaced
 * by polytypes) vs "non-specializable" ones (replaced only by monotypes).
 */
sealed class Type {
    /** A type variable, either specializable or non-specializable. */
    data class Var(val name: String) : Type() {
        override fun toString(): String = name
    }

    /** Arrow type: domain → codomain. */
    data class Arrow(val domain: Type, val codomain: Type) : Type() {
        override fun toString(): String {
            val domStr = when (domain) {
                is Arrow -> "($domain)"
                is Forall -> "($domain)"
                else -> "$domain"
            }
            return "$domStr → $codomain"
        }
    }

    /** Universal quantification: ∀α.body */
    data class Forall(val variable: String, val body: Type) : Type() {
        override fun toString(): String = "∀$variable.$body"
    }

    // ---- Convenience helpers ----

    fun freeVars(): Set<String> = when (this) {
        is Var -> setOf(name)
        is Arrow -> domain.freeVars() + codomain.freeVars()
        is Forall -> body.freeVars() - variable
    }

    /** Substitute [variable] with [replacement] (capture-avoiding). */
    fun substitute(variable: String, replacement: Type): Type = when (this) {
        is Var -> if (name == variable) replacement else this
        is Arrow -> Arrow(
            domain.substitute(variable, replacement),
            codomain.substitute(variable, replacement)
        )
        is Forall -> {
            if (this.variable == variable) {
                this // bound variable shadows; no substitution inside
            } else if (this.variable in replacement.freeVars()) {
                // capture-avoiding: rename bound variable
                val fresh = freshVar(this.variable, body.freeVars() + replacement.freeVars())
                val renamedBody = body.substitute(this.variable, Var(fresh))
                Forall(fresh, renamedBody.substitute(variable, replacement))
            } else {
                Forall(this.variable, body.substitute(variable, replacement))
            }
        }
    }

    /** Apply multiple substitutions simultaneously. */
    fun substitute(mapping: Map<String, Type>): Type {
        var result = this
        for ((v, t) in mapping) {
            result = result.substitute(v, t)
        }
        return result
    }

    companion object {
        private var counter = 0

        fun freshVar(base: String = "α", avoid: Set<String> = emptySet()): String {
            var candidate: String
            do {
                candidate = "${base}_${counter++}"
            } while (candidate in avoid)
            return candidate
        }

        fun resetCounter() {
            counter = 0
        }
    }
}
