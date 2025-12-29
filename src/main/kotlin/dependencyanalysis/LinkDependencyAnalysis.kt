package dependencyanalysis

import query.FlatApp
import query.Query
import util.Oracle

class LinkDependencyAnalysis(
    private val query: Query,
    private val arities: Map<String, Int>,
    private val oracle: Oracle
) {
    private val nodes =
        arities.flatMap { (name, arity) -> (0 until arity).map { ParameterNode(name, it) } }

    private fun nodes(name: String) = nodes.filter { it.f == name }

    val links: Map<String, List<Link>> by lazy { query.names.associateWith { findEdges(it) } }

    private fun findEdges(name: String): List<Link> {
        val arity = arities[name]!!
        val nullary = arity != 0
        val posExs = query.flatPosNoSubexprs(name)
        val negExs = query.flatNeg(name)

        // [argument index] to [witness] to [indices of corresponding positive examples]
        // posByArguments[i][arg] = set (or bitset) of blue tuple IDs
        val posByArguments = Array(arity) { mutableMapOf<FlatApp, MutableSet<Int>>() }
        posExs.forEachIndexed { exInd, pos ->
            pos.args.forEachIndexed { argIndex, arg ->
                posByArguments[argIndex].getOrPut(arg) { mutableSetOf() }.add(exInd)
            }
            /*
            // If the function was MORE than fully applied, the example up to the index at which it
            // was fully applied is a witness for the output type
            if (pos.args.size >= arity - 1) {
                val thepartialapplication = FlatApp(name, pos.args.take(arity - 1))
                posByArguments[arity - 1].getOrPut(TODO()) { mutableSetOf() }.add(TODO())
            }
             */
            /*
               Never mind.
               We can't find dependencies for output/nullary types this way, since we don't have
               negative examples for output types.
               We could do mayHaveFresh analysis for outputs.
               The old way is ok, but what about returning polymorphic nil or hofs?
               mayhavefresh doesn't really work for polymorphic nullaries but it's ok bc honestly i'm not sure it was
               that helpful to begin with idk maybe it was

        // TODO does mayhavefresh even work for HOFs either, I don't think so since they don't bind
        // variables
        //   so we may erroneously think a hole may have fresh when it is actually bound in a HOF
        // argument.
        // TODO if the first parameter is a function do we allow it to have infinite variables if it
        // has no constraint?
            */
        }

        val link = Array(arity) { Array(arity) { false } }
        negExs.forEach { neg ->
            for (i in 0 until arity) {
                val a = posByArguments[i][neg.args[i]] ?: emptySet()
                if (a.isEmpty()) continue
                for (j in 0 until arity) {
                    val b = posByArguments[j][neg.args[j]] ?: emptySet()
                    if (b.isEmpty()) continue
                    if (a != b || a.size > 1) {
                        link[i][j] = true
                    }
                }
            }
        }

        val links = mutableListOf<Link>()
        for (i in 0 until arity) {
            for (j in 0 until arity) {
                if (i <= j) continue
                if (link[i][j]) {
                    links.add(Link(i, j))
                }
            }
        }

        return links
    }
}

data class Link(val a: Int, val b: Int) {
    override fun toString(): String = "$a -- $b"

    override fun equals(other: Any?): Boolean =
        other is Link && ((other.a == a && other.b == b) || (other.a == b && other.b == a))

    override fun hashCode(): Int = a + b
}

/*
       fun exsInvolving(paramIndex: Int): List<FlatApp> =
           if (paramIndex < nodes.size - 1)
               posExs.filter { it.args.size > paramIndex && it.args.size < nodes.size }
           else posExs.filter { it.args.size == paramIndex }

       /** Requires: i is in bounds for ex. */
       fun arg(ex: FlatApp, paramIndex: Int) =
           if (paramIndex == ex.args.size) ex else ex.args[paramIndex]

       fun witnesses(paramIndex: Int): List<FlatApp> =
           exsInvolving(paramIndex).map { arg(it, paramIndex) }
*/
