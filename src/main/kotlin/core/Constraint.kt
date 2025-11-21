package core

import query.Example
import test.ConsTest
import util.Counter

/** ConstraintTypes are mutable */
sealed interface ConstraintType<L : Language> {
    val hasSubstitutable: Boolean
    fun substitutable(): List<Substitutable<L>>
}

sealed class CTypeConstructor<L : Language>(open val params: List<ConstraintType<L>>) : ConstraintType<L> {
    override val hasSubstitutable by lazy { params.any { it.hasSubstitutable } }
    override fun substitutable(): List<Substitutable<L>> = substitutable
    private val substitutable by lazy { params.flatMap { it.substitutable() } }
    abstract fun match(other: CTypeConstructor<L>): Boolean
    open fun split(other: CTypeConstructor<L>): List<Constraint<L>>? =
        if (match(other)) params.zip(other.params).map { (a, b) -> EqualityConstraint(a, b) } else null
}

sealed class CVariable<L : Language> : ConstraintType<L> {
    override val hasSubstitutable = false
    override fun substitutable(): List<Substitutable<L>> = listOf()
}

sealed class Substitutable<L : Language> : CVariable<L>() {
    override val hasSubstitutable = true
    override fun substitutable(): List<Substitutable<L>> = listOf(this)
}

data class CArrow<L : Language> constructor(override val params: List<ConstraintType<L>>) :
    CTypeConstructor<L>(params) {
    constructor(l: ConstraintType<L>, r: ConstraintType<L>) : this(listOf(l, r))

    val l = params[0]
    val r = params[1]

    override fun match(other: CTypeConstructor<L>) = other is CArrow<L>

    override fun toString() = "${if (l is CArrow) "($l)" else "$l"} -> $r"
}

/**
 * It is this class's job to instantiate its children once a commitment is made.
 * inst denotes _which_ instantiation we are in. This matters bc if we fill a hole with a variable,
 * that variable needs to know where it is so it matches the others in the same instantiation call. */
data class Instantiation<L : Language>(
    val n: Hole<L>, val holeId: Int, val uniqueId: Int, val inst: Int, val freshIdGen: Counter
) : CVariable<L>() {
    override fun toString() = "inst$holeId-$inst"
}

data class ProofVariable<L : Language>(val id: Int) : Substitutable<L>() {
    override fun toString() = "T$id"
}

sealed interface Constraint<L : Language> {
    fun trivial(): Boolean
    fun copy(): Constraint<L>
}

data class EqualityConstraint<L : Language>(var l: ConstraintType<L>, var r: ConstraintType<L>) : Constraint<L> {
    override fun toString() = "$l = $r"
    override fun trivial() = l == r || l is InitConstrV || r is InitConstrV
    fun substitutable() = l.substitutable() + r.substitutable()
    override fun equals(other: Any?): Boolean {
        return other is EqualityConstraint<*> && ((this.l == other.l && this.r == other.r) || (this.l == other.r && this.r == other.l))
    }

    override fun hashCode(): Int = l.hashCode() + r.hashCode()
    override fun copy() = EqualityConstraint(l, r)
}

typealias Commitment<L> = Pair<Hole<L>, SearchNode<L>>?

typealias UnificationForCandidate<L> = (Candidate<L>, List<Example>) -> Unification<L>

enum class UnificationTag {
    Eager, UnionFind, Constraint
}

fun <L : Language> unification(tag: UnificationTag): UnificationForCandidate<L> = when (tag) {
    UnificationTag.Eager -> ::EagerUnification
    UnificationTag.UnionFind -> ::UFUnification
    UnificationTag.Constraint -> ::ConstraintUnification
}

interface Unification<L : Language> {
    fun holeEqualsConstructors(hole: Int): List<CTypeConstructor<L>> =
        holeEquals(hole).filterIsInstance<CTypeConstructor<L>>()

    fun holeEqualsConstructors(hole: Hole<L>): List<CTypeConstructor<L>> =
        holeEqualsConstructors(hole.holeId)

    fun holeEquals(hole: Int): List<ConstraintType<L>>
    fun holeEquals(hole: Hole<L>): List<ConstraintType<L>> = holeEquals(hole.holeId)
    fun ok(): Boolean
    fun spawnAndRefine(refinements: List<Pair<Hole<L>, SearchNode<L>>>): Unification<L>

    /** Use me sparingly */
    fun constraints(): List<Constraint<L>>?
}

fun main() {
    val t = ConsTest
    println(t.query.names)
    val ty = Candidate(
        t.query.names, listOf(
            ConcreteL(0, listOf()),
            ConcreteL(1, listOf(ConcreteL(1, listOf(ConcreteL(0, listOf()))))),
            ConcreteL(1, listOf(ConcreteL(0, listOf()))),
            ConcreteL(1, listOf(ConcreteL(2, listOf()))),
            NArrow(
                ConcreteV(0), NArrow(
                    ConcreteL(1, listOf(ConcreteV(0))),
                    ConcreteL(1, listOf(ConcreteHole(false, null, mapOf(0 to 0, 1 to 1, 2 to 0)))),
                    false
                ), false
            ),
            ConcreteL(2, listOf())
        )
    )
    val constrs = ConstraintUnification(ty, t.query.posExsBeforeSubexprs).get()
    println(constrs)
}
