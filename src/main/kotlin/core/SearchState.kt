package core

import util.Counter
import util.lazyCartesianProduct

/** SearchNodes are functional and immutable... except for Holes. So they are not */
sealed interface SearchNode<L : Language> {
    fun instantiate(i: Counter, insts: Int): ConstraintType<L>
    fun expansions(): List<Pair<SearchNode<L>, Commitment<L>>>
    fun size(): Int
    fun depth(): Int
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
}

data class NArrow<L : Language> private constructor(override val params: List<SearchNode<L>>) :
    Branch<L>(params) {
    val l = params[0]
    val r = params[1]

    constructor(l: SearchNode<L>, r: SearchNode<L>) : this(listOf(l, r))

    override fun toString(): String = "${if (l is NArrow) "($l)" else "$l"} -> $r"

    override fun instantiate(i: Counter, insts: Int): ConstraintType<L> =
        CArrow(l.instantiate(i, insts), r.instantiate(i, insts))

    override fun expansions(): List<Pair<SearchNode<L>, Commitment<L>>> {
        // If we use prod, hole expansion cannot include itself, or blowup is too fast...
        // val prod = lazyCartesianProduct(listOf(params[0].expansions(), params[1].expansions())).map { NArrow(it) }
        val one = (l.expansions().map { (node, commit) -> NArrow(node, r) to commit } + r.expansions()
            .map { (node, commit) -> NArrow(l, node) to commit })
        return one.toSet().toList()
    }
}

sealed interface Leaf<L : Language> : SearchNode<L> {
    override fun expansions() = listOf(this to null)
    override fun size() = 1
    override fun depth() = 1
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

    fun expansions(constrs: List<Constraint<L>>): Sequence<Candidate<L>> { // TODO account for constraints
        // TODO should this be product, or also one at a time??
        return lazyCartesianProduct(types.map {
            // TODO this can be a mapNotNull, each expansion corresponds with assigning a hole to something
            //   concretizing an instantiation variable, then we can check against constrs, this lets us 
            //   use recursive constraints! But is it duplicate work now since we also check later? 
            //   If it is indeed duplicated, we can skip the call to make constraints at the head of 
            //   enumerate loop. It is better to use them here since one construction of constraints is used
            //   to prune many expansions. But I think it is necessary in both places... 
            //   Doing the pruning here just prevents us from keeping around garbage ones in the frontier

            it.expansions()
        }).mapNotNull {
//            val (types, commitments) = it.unzip()
//            if (Unification(constrs).commitAndCheckValid(commitments.filterNotNull()))
//                Candidate(names, types)
//            else {
//                println("Checking commitment helped here! Pruned ${Candidate(names, types)}")
//                null
//            }
            // TODO something is wrong here, we should accept cons: L -> V -> V but we don't

            Candidate(names, types)  // Originally
        }
    }
}
