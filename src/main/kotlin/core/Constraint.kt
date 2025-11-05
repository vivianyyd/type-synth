package core

import query.App
import query.Example
import query.Name
import test.ConsTest
import util.Counter
import util.UnionFind

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

    override fun match(other: CTypeConstructor<L>) = other is CArrow<L>

    override fun toString() = "${if (params[0] is CArrow) "(${params[0]})" else "${params[0]}"} -> ${params[1]}"
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

interface Unification<L : Language> {
    fun holeEquals(hole: Hole<L>): List<CTypeConstructor<L>>
    fun ok(): Boolean
    fun spawnAndRefine(refinements: List<Pair<Hole<L>, SearchNode<L>>>): Unification<L>

    /** Use me sparingly */
    fun constraints(): List<Constraint<L>>?
}

/** The unification that accepts everything. */
class Empty<L : Language> : Unification<L> {
    override fun holeEquals(hole: Hole<L>): List<CTypeConstructor<L>> = listOf()

    override fun spawnAndRefine(refinements: List<Pair<Hole<L>, SearchNode<L>>>): Unification<L> = this

    override fun ok(): Boolean = true

    override fun constraints(): List<Constraint<L>>? = listOf()
}

typealias Binding<L> = Pair<Substitutable<L>, ConstraintType<L>>

/** This unification does not persist state after evaluating a candidate, and cannot be used more than once. */
class EagerUnification<L : Language>(
    private val candidate: Candidate<L>,
    private val exs: List<Example>
) : Unification<L> {
    private var evaluated = false
    private var error = false
    private val customConstraints = mutableListOf<Constraint<L>>()
    private val holeConstraints = mutableMapOf<Hole<L>, MutableList<CTypeConstructor<L>>>()
    private var context = candidate.asMap

    private val instVarId = Counter()
    private val insts = Counter()  // Number of times any top-level type has been instantiated

    override fun holeEquals(hole: Hole<L>): List<CTypeConstructor<L>> =
        if (ok()) holeConstraints[hole] ?: listOf() else listOf()

    override fun ok(): Boolean {
        if (!evaluated) {
            error = exs.any {
                type(it) == null
            }
            evaluated = true
        }
        return !error
    }

    override fun spawnAndRefine(refinements: List<Pair<Hole<L>, SearchNode<L>>>): Unification<L> {
        val ref = refinements.toMap()
        fun refine(n: SearchNode<L>): SearchNode<L> = when (n) {
            is Hole -> ref[n] ?: n
            is Leaf -> n
            is ConcreteL -> ConcreteL(
                n.id,
                n.params.map { refine(it as SearchNode<L>) } as List<SearchNode<Concrete>>) as SearchNode<L>
            is NArrow -> NArrow(n.params.map { refine(it) }, n.contributesToDepth)
        }

        return EagerUnification(Candidate(candidate.names, candidate.types.map { refine(it) }), exs)
    }

    private fun type(ex: Example): ConstraintType<L>? {
        // build up custom constraints and hole constraints
        // for now, instantiate everything immediately. later i can think about lazy if it's slow
        return when (ex) {
            is Name -> context[ex.name]?.instantiate(instVarId, insts.get())
            is App -> type(ex.fn).let { f ->
                type(ex.arg)?.let { arg ->
                    when (f) {
                        is CArrow -> apply(f, arg)
                        is Instantiation -> {
                            holeConstraint(f, CArrow(arg, f))
                            // This is not actually the type, but the type is a hole, so let's just reuse the hole.
                            // This is okay because every time we commit, we start completely fresh.
                            f
                        }
                        else -> null
                    }
                }
            }
        }
    }

    fun apply(fn: CArrow<L>, arg: ConstraintType<L>): ConstraintType<L>? {
        val result = unify(fn.params.first(), arg)?.let {
            val out = if (fn.params.size == 2) fn.params[1] else CArrow(fn.params.drop(1))
            applyBindings(out, it)
        }
        return result
    }

    private fun holeConstraint(inst: Instantiation<L>, t: ConstraintType<L>) {
        if (t is CTypeConstructor<L>) holeConstraints.getOrPut(inst.n) { mutableListOf() }.add(t)
    }

    /** Returns a list of bindings resulting from unifying [arg] with [param], or null if they are incompatible. */
    private val unify = mutableMapOf<Pair<ConstraintType<L>, ConstraintType<L>>, List<Binding<L>>?>()
    fun unify(param: ConstraintType<L>, arg: ConstraintType<L>): List<Binding<L>>? {
        if ((param to arg) in unify) return unify[param to arg]
        val result = when (param) {
            is ProofVariable -> error("No proof variables arise in eager unification")
            is Substitutable ->
                if (param in arg.substitutable()) null
                else listOf(Binding(param, arg))
            is CTypeConstructor -> when (arg) {
                is ProofVariable -> error("No proof variables arise in eager unification")
                is CTypeConstructor -> {
                    val split = param.split(arg)
                    if (split == null) {
                        error = true
                        null // TODO check this is passed up correctly
                    } else {
                        val (equalities, custom) = split.partition { it is EqualityConstraint }
                        var bindings: MutableList<Binding<L>>? = mutableListOf()
                        (equalities as List<EqualityConstraint<L>>).forEach {
                            if (bindings != null) {
                                val l = applyBindings(it.l, bindings!!)
                                val r = applyBindings(it.r, bindings!!)
                                val u = unify(l, r)
                                if (u == null) bindings = null else bindings!!.addAll(u)
                            }
                        }
                        customConstraints.addAll(custom)
                        bindings
                    }
                }
                is Substitutable -> // for example, a function expects argument (int -> int) and we pass ('a -> 'a)
                    if (arg in param.substitutable()) null
                    else listOf(Binding(arg, param))
                InitConstrV -> listOf()
                is Instantiation -> {
                    holeConstraint(arg, param)
                    listOf()
                }
            }
            InitConstrV -> listOf()
            is Instantiation -> {
                holeConstraint(param, arg)
                listOf()
            }
        }
        unify[param to arg] = result
        return result
    }

    private val applyBinding =
        mutableMapOf<Triple<ConstraintType<L>, Substitutable<L>, ConstraintType<L>>, ConstraintType<L>>()

    fun applyBinding(
        t: ConstraintType<L>,
        v: Substitutable<L>,
        sub: ConstraintType<L>
    ): ConstraintType<L> {
        if (!t.hasSubstitutable) return t
        return applyBinding.getOrPut(Triple(t, v, sub)) {
            when (t) {
                is Substitutable -> if (t == v) sub else t
                is CTypeConstructor -> {
                    val p = t.params.map { applyBinding(it, v, sub) }
                    (when (t) {
                        is CArrow -> CArrow(p)
                        is ConcreteConstrL -> ConcreteConstrL(t.label, p as List<ConstraintType<Concrete>>)
                        InitConstrL, ElabConstrL, is ElaboratedConstrL -> error("hasSubstitutable should have been false")
                    } as ConstraintType<L>)
                }
                is Instantiation -> error("hasSubstitutable should have been false")
                is InitConstrV -> t
            }
        }
    }

    fun applyBindings(t: ConstraintType<L>, bindings: List<Binding<L>>): ConstraintType<L> =
        bindings.fold(t) { acc, (v, sub) -> applyBinding(acc, v, sub) }

    override fun constraints(): List<Constraint<L>>? = if (ok()) customConstraints else null
}

class UFUnification<L : Language> private constructor(
    private val uf: UnionFind<ConstraintType<L>> = UnionFind { it is CTypeConstructor<L> },
    private val instVarId: Counter = Counter(),
    private val proofVarId: Counter = Counter(),
    private var error: Boolean = false,
    private val insts: Counter = Counter(),  // Number of times any top-level type has been instantiated
    private val customConstraints: MutableList<Constraint<L>> = mutableListOf()
) : Unification<L> {
    constructor(candidate: Candidate<L>, exs: List<Example>) : this() {
        fun constrainType(ex: Example): ConstraintType<L> = when (ex) {
            is Name -> candidate.searchNodeOf(ex.name).instantiate(instVarId, insts.get())
            is App -> {
                val proofVariable = ProofVariable<L>(proofVarId.get())
                val a = constrainType(ex.fn)
                val b = CArrow(constrainType(ex.arg), proofVariable)
                unify(a, b)
                proofVariable
            }
        }
        exs.forEach { constrainType(it) }
        substs()
    }

    private fun unify(a: ConstraintType<L>, b: ConstraintType<L>) {
        val ta = uf.find(a)
        val tb = uf.find(b)
        if (ta is CTypeConstructor<L> && tb is CTypeConstructor<L>) {
            val (equalities, custom) = ta.split(tb)?.partition { it is EqualityConstraint } ?: run {
                error = true
                return
            }
            (equalities as List<EqualityConstraint<L>>).forEach { unify(it.l, it.r) }
            customConstraints.addAll(custom)
        } else if (ta is CVariable<L> || tb is CVariable<L>) {
            uf.union(ta, tb)
//            addReferences(ta)
//            addReferences(tb)
        } else throw Error("Cannot unify $a and $b: Something wrong with subtype casing")
    }

    override fun holeEquals(hole: Hole<L>): List<CTypeConstructor<L>> =
        uf.rootsFor { it is Instantiation && it.n == this }.filterIsInstance<CTypeConstructor<L>>()

    override fun spawnAndRefine(refinements: List<Pair<Hole<L>, SearchNode<L>>>): Unification<L> {
        val new = spawn()
        new.commitAndCheckValid(refinements)
        return new
    }

    private fun spawn() =
        UFUnification(
            uf.copy(),
            instVarId.copy(),
            proofVarId.copy(),
            error,
            insts.copy(),
            customConstraints.map { it.copy() }.toMutableList()
        )

    private fun commitAndCheckValid(refinements: List<Pair<Hole<L>, SearchNode<L>>>): Boolean {
        refinements.forEach { (hole, node) ->
            // for each instantiation variable for this node,
            uf.filterNodes { it is Instantiation && it in hole.instantiations() }
                .filterIsInstance<Instantiation<L>>(/*redundant but for cast*/).forEach {
                    // instantiate node with the correct ids and
                    // unify the instantiated replacement type with the canonical node of the inst
                    unify(uf.find(it), node.instantiate(it.freshIdGen, it.inst))
                    if (error) return false
                }
        }
        substs()
        return true
        // TODO we can remove proof variables from the eqclasses once they are resolved
    }

    override fun ok(): Boolean = !error

    /** Careful, I only return the custom ones! */
    override fun constraints(): List<Constraint<L>>? = if (error) null else customConstraints

    private fun substs() {
        // TODO make me less awful
        fun transform(t: ConstraintType<L>): ConstraintType<L> = when (t) {
            is CTypeConstructor -> {
                val p = t.params.map { transform(it) }
                (when (t) {
                    is CArrow -> CArrow(p)
                    is ConcreteConstrL -> ConcreteConstrL(t.label, p as List<ConstraintType<Concrete>>)
                    InitConstrL, ElabConstrL, is ElaboratedConstrL -> t
                } as ConstraintType<L>)
            }
            is Substitutable, is Instantiation -> uf.find(t)
            is InitConstrV -> t
        }
        // TODO I can use references to micro-opt
        val transformedRoots = uf.allRootValues().associateWith { transform(it) }
        // For each root, perform as many substs from variables to other roots as possible
        uf.replaceRoots(transformedRoots)
    }
}

class ConstraintUnification<L : Language> : Unification<L> {
    private val constraints = mutableListOf<Constraint<L>>()
    private var instVarId = Counter()
    private var proofVarId = Counter()
    private var error = false
    private var insts = Counter()  // Number of times any top-level type has been instantiated
    private val references = mutableMapOf<Substitutable<L>, MutableSet<EqualityConstraint<L>>>()

    constructor(constraints: List<Constraint<L>>) {
        this.constraints.addAll(constraints)
        constraints.filterIsInstance<EqualityConstraint<L>>().forEach { addReferences(it) }
    }

    constructor(candidate: Candidate<L>, exs: List<Example>) : this(listOf()) {
        fun constrainType(ex: Example): ConstraintType<L> = when (ex) {
            is Name -> candidate.searchNodeOf(ex.name).instantiate(instVarId, insts.get())
            is App -> {
                val proofVariable = ProofVariable<L>(proofVarId.get())
                val c = EqualityConstraint(constrainType(ex.fn), CArrow(constrainType(ex.arg), proofVariable))
                addReferences(c)
                constraints.add(c)
                proofVariable
            }
        }
        exs.forEach { constrainType(it) }
        simplify()
    }

    fun get(): List<Constraint<L>>? = if (error) null else constraints

    override fun constraints() = get()

    override fun ok() = !error

    override fun holeEquals(hole: Hole<L>): List<CTypeConstructor<L>> =
        constraints.filterIsInstance<EqualityConstraint<L>>().mapNotNull {
            if (it.l is Instantiation && (it.l as Instantiation<L>).n == hole) it.r
            else if (it.r is Instantiation && (it.r as Instantiation<L>).n == hole) it.l
            else null
        }.filterIsInstance<CTypeConstructor<L>>()

    private fun addReferences(c: EqualityConstraint<L>) {
        val substitutables = c.substitutable()
        substitutables.forEach {
            references.getOrPut(it) { mutableSetOf() }.add(c)
        }
    }

    private fun removeReferences(c: EqualityConstraint<L>) {
        val substitutables = c.substitutable()
        substitutables.forEach {
            references[it]!!.remove(c)
        }
    }

    override fun spawnAndRefine(refinements: List<Pair<Hole<L>, SearchNode<L>>>): Unification<L> {
        val new = spawn()
        new.commitAndCheckValid(refinements)
        return new
    }

    private fun spawn() = ConstraintUnification(constraints)

    private fun commitAndCheckValid(refinements: List<Pair<Hole<L>, SearchNode<L>>>): Boolean {
        betterCommit(refinements)
        if (error) refinements.forEach { it.first.conflict() }
        return !error
    }

    /**
    Optimization: Don't bother committing if running commit with those changes doesn't do anything.
    e.g. If we refine a hole to a fresh variable, store a list of commitments that we are delaying until later
     */
    private fun betterCommit(refinements: List<Pair<Hole<L>, SearchNode<L>>>): Boolean {
        val change = refinements.fold(false) { changed, (hole, node) ->
            var changedCurr = changed
            for (j in constraints.indices) {
                if (error) return false
                if (constraints[j] is EqualityConstraint<L>) {
                    val constr = constraints[j] as EqualityConstraint<L>

                    // TODO I am ugly and very bad. This should be a visitor pattern
                    fun newGuy(n: ConstraintType<L>): ConstraintType<L> = when (n) {
                        is Instantiation -> if (n in hole.instantiations()) node.instantiate(
                            n.freshIdGen, n.inst
                        ) else n
                        is CArrow -> CArrow(newGuy(n.params[0]), newGuy(n.params[1]))
                        is ConcreteConstrL -> ConcreteConstrL(
                            n.label,
                            n.params.map { newGuy(it as ConstraintType<L>) as ConstraintType<Concrete> }.toMutableList()
                        ) as ConstraintType<L>
                        is CVariable, InitConstrL, ElabConstrL, is ElaboratedConstrL -> n
                    }

                    val newL = newGuy(constr.l)
                    val newR = newGuy(constr.r)
                    val newC = EqualityConstraint(newL, newR)
                    constraints[j] = newC
                    removeReferences(constr)
                    addReferences(newC)
                    changedCurr = changedCurr || constr.l != newL || constr.r != newR
                }
            }
            changedCurr
        }
        simplify()
        return change
    }

    private fun simplify() {
        fun trivial() {
            constraints.removeAll {
                val t = it.trivial()
                if (t && it is EqualityConstraint<L>) removeReferences(it)
                t
            }
        }

        if (error) return
        val c1set = constraints.toSet()
        constraints.clear()
        constraints.addAll(c1set)
        var substChange = substs()
        var splitChange = splits()
        while (splitChange || substChange) {
            if (error) return
            trivial()
            val cset = constraints.toSet()
            constraints.clear()
            constraints.addAll(cset)
            substChange = if (splitChange) substs() else false
            splitChange = if (substChange) splits() else false
        }
        if (error) return
        trivial()
        val cset = constraints.toSet()
        constraints.clear()
        constraints.addAll(cset)
    }

    /** Replace [v] with [s] in [t] inplace. */
    private fun substitute(v: Substitutable<L>, s: ConstraintType<L>, t: ConstraintType<L>): ConstraintType<L> =
        when (t) {
            is Substitutable -> if (t == v) s else t
            is Instantiation -> t
            is CTypeConstructor -> {
                val p = t.params.map { substitute(v, s, it) }
                (when (t) {
                    is CArrow -> CArrow(p)
                    is ConcreteConstrL -> ConcreteConstrL(t.label, p as List<ConstraintType<Concrete>>)
                    InitConstrL, ElabConstrL, is ElaboratedConstrL -> t
                } as ConstraintType<L>)

            }

            is InitConstrV -> t
        }

    private fun substs(): Boolean {
        val substs = constraints.filterIsInstance<EqualityConstraint<L>>()
            .filter { it.l is Substitutable || it.r is Substitutable }.map { eq ->
                val v: Substitutable<L> =
                    if (eq.l is ProofVariable) eq.l as ProofVariable<L>
                    else (if (eq.r is ProofVariable) eq.r
                    else if (eq.l is Substitutable) eq.l
                    else (eq.r as Substitutable)) as Substitutable<L>
                val s = if (eq.l == v) eq.r else eq.l
                Triple(eq, v, s)
            }
        substs.forEach { (eq, v, s) ->
            val refs = references[v]!!.toSet()  // avoids concurrentmodificationexception
            refs.forEach {
                if (it != eq) {
                    removeReferences(it)
                    it.l = substitute(v, s, it.l)
                    it.r = substitute(v, s, it.r)
                    addReferences(it)
                }
            }
        }
        // Because we make modifications inplace, we need to check that the constraint is even the same as when we began
        val toRemove =
            substs.mapNotNull { (eq, v, s) -> if (v is ProofVariable<*> && ((eq.l == v && eq.r == s) || eq.r == v && eq.l == s)) eq else null }
        constraints.removeAll {
            if (it in toRemove && it is EqualityConstraint<L>) removeReferences(it)
            it in toRemove
        }
        return substs.isNotEmpty()
    }

    private fun splits(): Boolean {
        val newConstrs = mutableListOf<Constraint<L>>()
        fun splittable(c: Constraint<L>) =
            c is EqualityConstraint<L> && c.l is CTypeConstructor<L> && c.r is CTypeConstructor<L>

        /** @returns new constraints from splitting [c], or [c] if it was not split. */
        fun split(c: EqualityConstraint<L>): List<Constraint<L>> {
            if (splittable(c)) {
                val result = (c.l as CTypeConstructor<L>).split(c.r as CTypeConstructor<L>)
                if (result == null) {
                    error = true
                    return listOf(c)
                }
                return result.filter { it !is EqualityConstraint } + result.filterIsInstance<EqualityConstraint<L>>()
                    .flatMap { split(it) }
            }
            return listOf(c)
        }

        for (constr in constraints.filterIsInstance<EqualityConstraint<L>>()) {
            if (splittable(constr)) {
                val tmp = split(constr)
                if (error) return false
                newConstrs.addAll(tmp)
            }
        }
        if (error) return false
        val changed = constraints.removeAll {
            val r = splittable(it)
            if (r && it is EqualityConstraint<L>) removeReferences(it)
            r
        }
        newConstrs.filterIsInstance<EqualityConstraint<L>>().forEach { addReferences(it) }
        constraints.addAll(newConstrs)
        return changed
    }
}

/*
Handling conflicts:
- conflict analysis - small set of assignments in DAG that separates conflict from roots (cut)
- two literal watching - only check clauses for which the variable set is one of the two that is being watched
    I think we cannot really do this but maybe it's not so bad bc each constraint has at most two inst() nodes
 */

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
