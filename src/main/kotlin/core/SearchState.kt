package core

import util.Counter
import util.lazyCartesianProduct

/** SearchNodes are functional and immutable... except for Holes. So they are not
 * Only full types are hashable */
sealed interface SearchNode<L : Language> {
    fun instantiate(i: Counter, insts: Int): ConstraintType<L>
    fun expansions(constrs: List<Constraint<L>> = listOf()): List<Pair<SearchNode<L>, Commitment<L>>>
    fun size(): Int
    fun depth(): Int
    fun full(): Boolean

    /** Optional for correctness, but helps us recognize alpha equivalences */
    fun variableNames(): Set<Int>
    fun canonical() = variableNames().size == (variableNames().maxOrNull() ?: -1) + 1
}

sealed class Branch<L : Language>(open val params: List<SearchNode<L>>) : SearchNode<L> {
    init {
//        TODO(
//            "params should actually be private, and we only allow params if they have the same arity" +
//                    "whatever. or we only support pruning operation or something idk. think of how it interacts " +
//                    "with holes"
//        )
//        TODO("maybe this can be an interface w functions and no params value")
    }

    override fun size() = size
    private val size by lazy {
        1 + params.sumOf { it.size() }
    }

    override fun depth() = depth
    private val depth by lazy {
        1 + params.maxOf { it.depth() }
    }

    override fun full() = params.all { it.full() }

    override fun variableNames() = params.flatMap { it.variableNames() }.toSet()
}

data class NArrow<L : Language> private constructor(override val params: List<SearchNode<L>>) :
    Branch<L>(params) {
    open val l = params[0]
    open val r = params[1]

    constructor(l: SearchNode<L>, r: SearchNode<L>) : this(listOf(l, r))

    override fun toString(): String = "${if (l is NArrow) "($l)" else "$l"} -> $r"

    override fun instantiate(i: Counter, insts: Int): ConstraintType<L> =
        CArrow(l.instantiate(i, insts), r.instantiate(i, insts))

    override fun expansions(constrs: List<Constraint<L>>): List<Pair<SearchNode<L>, Commitment<L>>> {
        // If we use prod, hole expansion cannot include itself, or blowup is too fast...
        // val prod = lazyCartesianProduct(listOf(params[0].expansions(), params[1].expansions())).map { NArrow(it) }
        val one = (l.expansions(constrs).map { (node, commit) -> NArrow(node, r) to commit } + r.expansions(constrs)
            .map { (node, commit) -> NArrow(l, node) to commit })
        return one.toSet().toList()
    }
}

sealed interface Leaf<L : Language> : SearchNode<L> {
    override fun expansions(constrs: List<Constraint<L>>): List<Pair<SearchNode<L>, Commitment<L>>> =
        listOf(this to null)

    override fun size() = 1
    override fun depth() = 1
    override fun full() = true
}

sealed class Hole<L : Language> : SearchNode<L> {
    private val instantiations = mutableListOf<Instantiation<L>>()

    override fun instantiate(i: Counter, insts: Int): ConstraintType<L> {
        val inst = Instantiation(this, i.get(), insts, i)
        instantiations.add(inst)
        return inst
    }

    fun instantiations(): List<Instantiation<L>> = instantiations

    override fun size() = 1
    override fun depth() = 0
    override fun full() = false
    override fun variableNames() = emptySet<Int>()
    override fun toString() = "_"
}

data class Candidate<L : Language>(val names: List<String>, val types: List<SearchNode<L>>) {
    override fun toString(): String =
        names.zip(types).joinToString(separator = ", ") { "${it.first}: ${it.second}" }

    fun searchNodeOf(name: String): SearchNode<L> = types[names.indexOf(name)]

    val size by lazy {
        types.sumOf { it.size() }
    }

    val depth by lazy {
        types.maxOf { it.depth() }
    }

    fun full() = types.all { it.full() }

    fun canonical() = types.all { it.canonical() }

    fun expansions(constrs: List<Constraint<L>> = listOf()): Sequence<Candidate<L>> {
        // TODO should this be product, or also one at a time?? either will work but what is better
        return lazyCartesianProduct(types.map {
            // Each expansion corresponds with concretizing one hole. We check constrs after refining corresponding inst
            // variables, this lets us check w inherited constrs from parent. If we can elim many this way, we save a
            // lot of space from not keeping around bad candidates in frontier only to find they are bad later.
            // We also use one construction of constraints to prune many expansions
            it.expansions(constrs)
        }).mapNotNull {
            val (types, commitments) = it.unzip()
            if (Unification(constrs).commitAndCheckValid(commitments.filterNotNull()))
                Candidate(names, types)
            else null  // Could count here for eval
//            Candidate(names, types)  // Originally
        }
    }
}
