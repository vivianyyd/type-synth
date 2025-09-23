package core

import util.Counter

sealed interface SearchNode<L : Language> {
    fun instantiate(i: Counter): ConstraintType<L>
}

sealed class Branch<L : Language>(open val params: MutableList<SearchNode<L>>) : SearchNode<L> {
    init {
        TODO(
            "params should actually be private, and we only allow params if they have the same arity" +
                    "whatever. or we only support pruning operation or something idk. think of how it interacts " +
                    "with holes"
        )
        TODO("maybe this can be an interface w functions and no params value")
    }
}

sealed interface Leaf<L : Language> : SearchNode<L>

class Hole<L : Language>(val options: MutableList<SearchNode<L>>) : SearchNode<L> {
    private val instantiations = mutableListOf<Instantiation<L>>()

    override fun instantiate(i: Counter): ConstraintType<L> {
        val inst = Instantiation(this, i.get())
        instantiations.add(inst)
        return inst
    }
}

class SearchState<L : Language> {
    fun searchNodeOf(name: String): SearchNode<L> = TODO()
}

