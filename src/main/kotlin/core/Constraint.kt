package core

sealed interface ConstraintType<L : Language>
sealed class CTypeConstructor<L : Language>(open val params: MutableList<ConstraintType<L>>) : ConstraintType<L> {
    abstract fun lineup(other: CTypeConstructor<*>): List<Constraint<L>>
}

sealed interface CVariable<L : Language> : ConstraintType<L>
sealed interface Substitutable

data class CArrow<L : Language> private constructor(override val params: MutableList<ConstraintType<L>>) :
    CTypeConstructor<L>(params) {
    constructor(l: ConstraintType<L>, r: ConstraintType<L>) : this(mutableListOf(l, r))

    override fun lineup(other: CTypeConstructor<*>): List<Constraint<L>> {
        if (other is CArrow<*>) {
            if (this.javaClass == other.javaClass) params.map { }
            else TODO()
        } else TODO()
    }
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
        val newConstrs = constraints.filter { it.l is CTypeConstructor<*> && it.r is CTypeConstructor<*> }.flatMap {
            (it.l as CTypeConstructor<*>).lineup(it.r as CTypeConstructor<*>)
        }
        // TODO: When constraints have matching type constructors, split them up appropriately
    }
}

object CInitVar : CVariable<Init>