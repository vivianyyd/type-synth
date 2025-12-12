package core.unification

import core.languages.*
import query.App
import query.Example
import query.Name
import util.Counter

typealias Binding<L> = Pair<Substitutable<L>, ConstraintType<L>>

/** This unification does not persist state after evaluating a candidate, and cannot be used more than once. */
class EagerUnification<L : Language>(
    private val candidate: Candidate<L>,
    private val exs: List<Example>
) : Unification<L> {
    private var evaluated = false
    private var error = false
    private val customConstraints = mutableListOf<Constraint<L>>()
    private val holeConstraints = mutableMapOf<Int, MutableList<ConstraintType<L>>>()  // holeId
    private var context = candidate.asMap

    private val instVarId = Counter()
    private val insts = Counter()  // Number of times any top-level type has been instantiated

    override fun holeEquals(hole: Int): List<ConstraintType<L>> =
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
            is NArrow -> NArrow(n.params.map { refine(it) }, n.contributesToDepth)
            is ConcreteL -> ConcreteL(
                n.id,
                n.params.map { refine(it as SearchNode<L>) } as List<SearchNode<Concrete>>) as SearchNode<L>
        }

        return EagerUnification(Candidate(candidate.names, candidate.types.map { refine(it) }), exs)
    }

    private fun type(ex: Example): ConstraintType<L>? = when (ex) {
        // for now, instantiate everything immediately. later i can think about lazy if it's slow
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

    fun apply(fn: CArrow<L>, arg: ConstraintType<L>): ConstraintType<L>? =
        unify(fn.l, arg)?.let {
            applyBindings(fn.r, it)
        }

    private fun holeConstraint(inst: Instantiation<L>, t: ConstraintType<L>) {
        holeConstraints.getOrPut(inst.n.holeId) { mutableListOf() }.add(t)
    }

    /** Returns a list of bindings resulting from unifying [arg] with [param], or null if they are incompatible. */
    fun unify(param: ConstraintType<L>, arg: ConstraintType<L>): List<Binding<L>>? = when (param) {
        is Substitutable ->
            if (param in arg.substitutable()) null
            else listOf(Binding(param, arg))
        is CTypeConstructor -> when (arg) {
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

    fun applyBinding(
        t: ConstraintType<L>,
        v: Substitutable<L>,
        sub: ConstraintType<L>
    ): ConstraintType<L> {
        if (!t.hasSubstitutable) return t
        return when (t) {
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

    fun applyBindings(t: ConstraintType<L>, bindings: List<Binding<L>>): ConstraintType<L> =
        bindings.fold(t) { acc, (v, sub) -> applyBinding(acc, v, sub) }

    override fun constraints(): List<Constraint<L>>? = if (ok()) customConstraints else null
}
