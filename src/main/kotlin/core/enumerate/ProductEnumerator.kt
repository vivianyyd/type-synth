package core.enumerate

import core.Candidate
import core.Language
import core.SearchNode
import query.Query

data class PortNode<L : Language>(val options: List<MutableList<PortNode<L>>>) {

}

class ProductEnumerator<L : Language>(
    val query: Query,
    override val seedCandidate: Candidate<L>,
    private val mustPassNegatives: Boolean,
    val depth: (Candidate<L>) -> Int,
    private val minimizeSize: Boolean = false
) : Enumerator<L> {
    private val state = mutableListOf<SearchNode<L>>()

    init {
        TODO()
    }

    fun step(): List<List<SearchNode<L>>> {
        val sols = mutableListOf<List<SearchNode<L>>>()
        state.forEach {
            /*
            If it's an arrow,
                if its depth is greater than both child's depth,
                    enumerate normally (call enumerate on this node directly; default recursion bound is fine)
                Otherwise,
                    call step param on left child (calls normal enumerate with default recursion bound)
                    recurse this special casing on right child
             */
        }
        TODO()
    }

    override fun enumerate(sizeBound: Int, hardDepthBound: Int): List<Candidate<L>> {
        TODO()


//        // 1. Get constraints for each function from Unification
//        val constrs = unification(seedCandidate, query.posExsBeforeSubexprs).get() ?: return listOf()
//        // 2. For each function, enumerate possible building blocks (expansions)
//        val optionsPerFunction = seedCandidate.types.mapIndexed { i, node ->
//            node.expansions(constrs, node.variableNames(), maxDepth).map { it.first }
//        }
//        // 3. Generate all combinations (cartesian product) of building blocks
//        val candidates = lazyCartesianProduct(optionsPerFunction).map { Candidate(seedCandidate.names, it) }
//        // 4. Filter candidates by constraints and examples
//        return candidates.filter { c ->
//            c.canonical() &&
//                    unification(c, query.posExsBeforeSubexprs).get() != null &&
//                    (if (mustPassNegatives) query.negExamples.all {
//                        unification(c, listOf(it)).get() == null
//                    } else true)
//        }.toList()
    }
}
