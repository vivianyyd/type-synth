package baselines.lc

/**
 * Robinson's unification algorithm for types.
 *
 * Conventions:
 *   - A Type.Var whose name starts with an uppercase letter (e.g., "Int", "Bool")
 *     is treated as a TYPE CONSTANT — it only unifies with itself.
 *   - A Type.Var whose name contains '_' is an INTERNAL (generated) variable.
 *     These are preferentially bound over user-named variables.
 *   - A Type.Var whose name is lowercase (e.g., "a", "b") is a regular type variable.
 */
object Unification {

    fun unify(t1: Type, t2: Type): Substitution? =
        unifyAccum(listOf(t1 to t2), Substitution.empty)

    private fun unifyAccum(
        worklist: List<Pair<Type, Type>>,
        currentSubst: Substitution
    ): Substitution? {
        if (worklist.isEmpty()) return currentSubst
        val (t1Raw, t2Raw) = worklist.first()
        val rest = worklist.drop(1)
        val t1 = currentSubst.apply(t1Raw)
        val t2 = currentSubst.apply(t2Raw)

        return when {
            t1 == t2 -> unifyAccum(rest, currentSubst)

            // Two variables: bind internal before user, never bind two constants together
            t1 is Type.Var && t2 is Type.Var -> {
                val t1Const = isConstant(t1.name)
                val t2Const = isConstant(t2.name)
                when {
                    t1Const && t2Const -> null // two distinct constants
                    t1Const -> bind(t2.name, t1, rest, currentSubst)
                    t2Const -> bind(t1.name, t2, rest, currentSubst)
                    isInternal(t1.name) -> bind(t1.name, t2, rest, currentSubst)
                    isInternal(t2.name) -> bind(t2.name, t1, rest, currentSubst)
                    else -> bind(t1.name, t2, rest, currentSubst)
                }
            }

            // Variable on one side — bind it (unless it's a constant vs compound)
            t1 is Type.Var -> {
                if (isConstant(t1.name)) null  // constant can't be an arrow
                else if (occursIn(t1.name, t2)) null
                else bind(t1.name, t2, rest, currentSubst)
            }

            t2 is Type.Var -> {
                if (isConstant(t2.name)) null
                else if (occursIn(t2.name, t1)) null
                else bind(t2.name, t1, rest, currentSubst)
            }

            t1 is Type.Arrow && t2 is Type.Arrow -> unifyAccum(
                listOf(t1.domain to t2.domain, t1.codomain to t2.codomain) + rest,
                currentSubst
            )

            else -> null
        }
    }

    private fun bind(
        name: String, target: Type,
        rest: List<Pair<Type, Type>>, currentSubst: Substitution
    ): Substitution? {
        if (occursIn(name, target)) return null
        val newSubst = Substitution(mapOf(name to target))
        return unifyAccum(rest, newSubst.compose(currentSubst))
    }

    /** Internal (generated) variable names contain '_'. */
    internal fun isInternal(name: String): Boolean = '_' in name

    /** Type constants start with uppercase (e.g., "Int", "Bool", "Nat"). */
    internal fun isConstant(name: String): Boolean =
        name.isNotEmpty() && name[0].isUpperCase() && '_' !in name

    fun occursIn(name: String, type: Type): Boolean = when (type) {
        is Type.Var -> type.name == name
        is Type.Arrow -> occursIn(name, type.domain) || occursIn(name, type.codomain)
        is Type.Forall -> if (type.variable == name) false else occursIn(name, type.body)
    }
}
