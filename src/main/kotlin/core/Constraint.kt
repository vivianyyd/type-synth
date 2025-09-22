package core

sealed interface ConstraintType<L : Language>
sealed class CTypeConstructor<L : Language>(open val params: MutableList<ConstraintType<L>>) : ConstraintType<L> {
    abstract fun match(other: CTypeConstructor<L>): Boolean
    fun lineup(other: CTypeConstructor<L>): List<Constraint<L>>? =
        if (match(other)) params.zip(other.params).map { (a, b) -> Constraint(a, b) } else null
}

sealed interface CVariable<L : Language> : ConstraintType<L>
sealed interface Substitutable

data class CArrow<L : Language> private constructor(override val params: MutableList<ConstraintType<L>>) :
    CTypeConstructor<L>(params) {
    constructor(l: ConstraintType<L>, r: ConstraintType<L>) : this(mutableListOf(l, r))

    override fun match(other: CTypeConstructor<L>) = other is CArrow<L>
}

data class Instantiation<L : Language>(val n: SearchNode) : CVariable<L> // TODO node or an id?
data class ProofVariable<L : Language>(val id: Int) : CVariable<L>, Substitutable

data class Constraint<L : Language>(val l: ConstraintType<L>, val r: ConstraintType<L>)

class Unification<L : Language>(constraints: List<Constraint<L>>) {
    val constraints = constraints.toMutableList()

    /** Replace [v] with [s] in [t]. */
    private fun replace(v: Substitutable, s: ConstraintType<L>, t: ConstraintType<L>): ConstraintType<L> =
        when (t) {
            is Substitutable -> if (t == v) s else t
            is Instantiation -> t
            is CTypeConstructor -> {
                t.params.replaceAll { replace(v, s, it) }
                t
            }
        }

    fun substs() {
        for (i in constraints.indices) {
            val curr = constraints[i]
            if (curr.l is Substitutable || curr.r is Substitutable) {
                val v: Substitutable = if (curr.l is Substitutable) curr.l else (curr.r as Substitutable)
                val s = if (curr.l is Substitutable) curr.r else curr.l
                for (j in constraints.indices) {
                    constraints[j] = Constraint(
                        replace(v, s, constraints[j].l),
                        replace(v, s, constraints[j].r)
                    )
                }
            }
        }
        constraints.removeAll { it.l is Substitutable || it.r is Substitutable }
    }

    fun splits() {
        var success = true
        val newConstrs = mutableListOf<Constraint<L>>()
        for (constr in constraints.filter { it.l is CTypeConstructor<L> && it.r is CTypeConstructor<L> }) {
            val result = (constr.l as CTypeConstructor<L>).lineup(constr.r as CTypeConstructor<L>)
            if (result == null) {
                success = false
                break
            }
            newConstrs.addAll(result)
        }
        if (!success) TODO()
        constraints.removeAll { it.l is CTypeConstructor<L> && it.r is CTypeConstructor<L> }
        constraints.addAll(newConstrs)
    }
}

//object CInitVar : CVariable<Init>