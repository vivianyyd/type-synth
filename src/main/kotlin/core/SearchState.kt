package core

import util.Counter
import util.lazyCartesianProduct

sealed interface SearchNode<L : Language> {
    fun instantiate(i: Counter, insts: Int): ConstraintType<L>
    fun expansions(): List<SearchNode<L>>
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
    constructor(l: SearchNode<L>, r: SearchNode<L>) : this(listOf(l, r))

    override fun toString(): String = "${if (params[0] is NArrow) "(${params[0]})" else "${params[0]}"} -> ${params[1]}"

    override fun instantiate(i: Counter, insts: Int): ConstraintType<L> =
        CArrow(params[0].instantiate(i, insts), params[1].instantiate(i, insts))

    override fun expansions(): List<SearchNode<L>> { // TODO account for constraints
        return lazyCartesianProduct(listOf(params[0].expansions(), params[1].expansions())).map { NArrow(it) }.toList()
    }
}

sealed interface Leaf<L : Language> : SearchNode<L> {
    override fun expansions() = listOf(this)
    override fun size() = 1
    override fun depth() = 1
}

sealed class Hole<L : Language>(val options: List<SearchNode<L>>) : SearchNode<L> {
    private val instantiations = mutableListOf<Instantiation<L>>()

    override fun instantiate(i: Counter, insts: Int): ConstraintType<L> {
        val inst = Instantiation(this, i.get())
        instantiations.add(inst)
        return inst
    }

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

    fun expansions(constrs: List<Constraint<L>>): List<Candidate<L>> { // TODO account for constraints
        return lazyCartesianProduct(types.map { it.expansions() }).map { Candidate(names, it) }.toList()
    }

//    abstract fun initNext(): Candidate<Language>  // todo types here are weird unless I want successor to be one of typarams
//    inline fun <reified Succ : Language> initNext() = initNext(Succ::class)
}
