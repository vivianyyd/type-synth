package baselines.lc

/**
 * SUP (Semi-Unification Problem) and its subproblems ASUP and R-ASUP.
 *
 * Definition 1 (SUP): Given a finite algebra A, an instance of SUP is a set C of pairs
 * (called inequalities) {τ₁ ≤ μ₁, ..., τₙ ≤ μₙ} where τᵢ, μᵢ ∈ A for all i.
 * A solution of C is a substitution S such that there exist substitutions S₁,...,Sₙ
 * such that SᵢSτᵢ = Sμᵢ for each i.
 *
 * For type inference:
 * - Equalities τ = μ are sugar for: τ ≤ μ where μ is a fresh variable (so the solver
 *   must unify them)
 * - The algebra A is the set of types built from type variables and →
 */

/** An inequality τ ≤ μ in a SUP instance. */
data class Inequality(val lhs: Type, val rhs: Type) {
    override fun toString(): String = "$lhs ≤ $rhs"
}

/** An equality τ = μ, which is sugar for the inequality α ≤ τ ≤ μ ≤ α pattern. */
data class Equality(val lhs: Type, val rhs: Type) {
    override fun toString(): String = "$lhs = $rhs"
}

/**
 * A constraint is either an inequality (τ ≤ μ) or an equality (τ = μ).
 * Equalities are expanded to pairs of inequalities during translation.
 */
sealed class Constraint {
    data class Ineq(val inequality: Inequality) : Constraint()
    data class Eq(val equality: Equality) : Constraint()
}

/**
 * An R-ASUP instance: the acyclic semi-unification problem restricted
 * to instances whose SUP graphs are R-acyclic.
 *
 * Definition 2: Given an ASUP instance Γ, the SUP graph G(Γ) is a directed graph where:
 *   - vertices are the inequalities τ ≤ μ
 *   - green vertices (inequalities) τᵢ ≤ μᵢ and τⱼ ≤ μⱼ:
 *     there is an edge from μᵢ to τⱼ (i.e., μᵢ and τⱼ share structure)
 *
 * R-ASUP is a decidable subset of SUP, and Algorithm LC produces R-ASUP instances.
 *
 * Variables are partitioned into:
 *   - "specializable" (s-variables): may be substituted with polytypes
 *   - "non-specializable" (n-variables): may only be substituted with monotypes
 */
data class RAsupInstance(
    val inequalities: List<Inequality>,
    val equalities: List<Equality>,
    /** Variables that are specializable (can be replaced by polytypes). */
    val specializableVars: Set<String>,
    /** Variables that are non-specializable (monotype only). */
    val nonSpecializableVars: Set<String>
) {
    override fun toString(): String {
        val ineqs = inequalities.joinToString("\n  ") { it.toString() }
        val eqs = equalities.joinToString("\n  ") { it.toString() }
        return "R-ASUP Instance:\n  Inequalities:\n  $ineqs\n  Equalities:\n  $eqs"
    }
}

/**
 * A substitution mapping variable names to types.
 */
data class Substitution(val mapping: Map<String, Type> = emptyMap()) {

    fun apply(type: Type): Type = type.substitute(mapping)

    fun apply(ineq: Inequality): Inequality =
        Inequality(apply(ineq.lhs), apply(ineq.rhs))

    fun compose(other: Substitution): Substitution {
        // (this ∘ other): first apply other, then this
        val newMapping = other.mapping.mapValues { (_, v) -> apply(v) } + mapping
        return Substitution(newMapping)
    }

    companion object {
        val empty = Substitution()
    }
}
