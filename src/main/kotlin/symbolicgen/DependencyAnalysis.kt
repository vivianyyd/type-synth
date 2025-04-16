package symbolicgen

import symbolicgen.symbolicsketcher.F
import symbolicgen.symbolicsketcher.SpecializedSymbolicType
import symbolicgen.symbolicsketcher.Var
import util.*
import java.lang.Integer.max

sealed interface DependencyConstraint

// TODO MustContainVariables, MustSuperSet/SubSet. Currently don't really know how to use these anyway
//   so not implemented yet
object ContainsNoVariables : DependencyConstraint
data class ContainsOnly(val vId: Int, val tId: Int) : DependencyConstraint

/*
 * TODO:
 *  Inputs are functions and arities (manually write for now, then write analysis for this)
 *  Visualizer for dep graphs
 */
class DependencyAnalysis(
    private val query: NewQuery,
    outline: Map<String, SpecializedSymbolicType>,
    private val oracle: EqualityNewOracle
) {
    val nodeToType = outline.entries.fold(mutableMapOf<ParameterNode, SpecializedSymbolicType>()) { m, (name, tree) ->
        var curr = tree
        var count = 0
        while (curr is F) {
            m[ParameterNode(name, count)] = curr.left
            count++
            curr = curr.rite
        }
        m[ParameterNode(name, count)] = curr
        m
    }

    val nodes: Set<ParameterNode> = nodeToType.keys

    fun nodes(name: String) = nodes.filter { it.f == name }

    val graphs: Map<String, DependencyGraph> by lazy {
        query.names.associateWith { name ->
            val (deps, loops) = findEdges(name)
            DependencyGraph(name, nodes.filter { it.f == name }.toSet(), deps, loops)
        }
    }

    fun constraints(name: String): Map<Int, DependencyConstraint> {
        val graph = graphs[name]!!
        val constrs = mutableMapOf<Int, DependencyConstraint>()
        graph.loops.forEach {
            constrs[it.a.i] = ContainsNoVariables
        }
        graph.deps.forEach {
            val sup = nodeToType[it.sup]!!
            if (sup is Var) constrs[it.sub.i] = ContainsOnly(sup.vId, sup.tId)
        }
        return constrs
    }

    /**
     * A map from function names to a list of sequences of applications with that name as the leftmost function,
     * from smallest to largest by containment
     * e.g. If positive examples are (f 0) and (f 1 2), produces {f: [[(f 0)], [(f 1), (f 1 2)]]}
     * So for each of the internal lists, index i includes applications up to the ith argument.
     * TODO this is super inefficient. Should instead flatten all examples to be like the old Application version
     */
    val examples =
        query.posExamples.fold(query.names.associateWith<String, MutableList<List<App>>> { mutableListOf() }) { acc, ex ->
            var curr = ex
            val apps = mutableListOf<App>()
            while (curr is App) {
                apps.add(curr)
                curr = curr.fn
            }
            apps.reverse()
            val name = (curr as Name).name
            if (apps.isNotEmpty()) acc[name]!!.add(apps)
            acc
        }

    private fun findEdges(name: String): Pair<Set<DependencyEdge>, Set<SelfLoop>> {
        val nodes = nodes(name)
        val deps = mutableSetOf<DependencyEdge>()
        val loops = mutableSetOf<SelfLoop>()

        // TODO note we assume we have all subexprs in posExamples here
        val posExs = examples[name]!!
        val negExs = query.negExamples
        val parameters = nodes.filter { it.f == name }
        for (pi in parameters) {
            for (pj in parameters) {
                val i = pi.i
                val j = pj.i

                // Skip half the pairs since links are undirected. We'll do both directions of deps at once below
                if (j < i) continue

                fun param(index: Int, ex: List<App>): Example = if (index < nodes.size - 1) {
                    assert(ex.size > index)
                    ex[index].arg
                } else {
                    assert(ex.size >= index)
                    ex[index - 1]
                }

                val relevantExs = max(i, j).let { m ->
                    if (m < nodes.size - 1) posExs.filter { it.size > m } else posExs.filter { it.size >= m }
                }

                /** all examples of the [index]th parameter. requires that parameter exists in all examples in [exs]. */
                fun params(index: Int) = relevantExs.map { param(index, it) }

                if (i == j) {
                    if (equivalenceClasses(params(i), oracle::equal).size == 1) {
                        loops.add(SelfLoop(pi))
                    }
                } else {
                    // Do both directions of dependency edges
                    fun depEdge(source: Int, sink: Int): Boolean {
                        val groupedBySink = equivalenceClasses(relevantExs) { e1, e2 ->
                            oracle.equal(param(sink, e1), param(sink, e2))
                        }
                        val sourceChangesWhileSinkConstant = groupedBySink.any { eqClass ->
                            eqClass.any {
                                val arbitraryElem = param(source, eqClass.first())
                                !oracle.equal(param(source, it), arbitraryElem)
                            }
                        }
                        return !sourceChangesWhileSinkConstant
                    }
                    if (depEdge(i, j)) {
                        deps.add(DependencyEdge(pi, pj))
                    }
                    if (depEdge(j, i)) {
                        deps.add(DependencyEdge(pj, pi))
                    }
                }
            }
        }
        return Pair(deps, loops)
    }
    /*
    ## Undirected links:
    Two dual algorithms. Pick one depending on num posexs vs negexs.
        (We'll eventually make tons of negexs? Or generate them as needed. That might work in here nicely)

        Start with empty graph (empty but upper triang)
        For valid arg ai to xi
            For valid arg aj to xj
                 Look for negex where ai, aj used in xi, xj
                 If one exists, add a link edge at ij

        For all negexs with ai for xi, aj for xj
            Check if ai, aj are otherwise valid inputs to xi, xj
            Maybe this is faster bc only have to read each negex once idk

    ## Bidirectional dependencies:
    Start with complete graph (full adj matrix - not triangular)
    Proceed row by row
    For xi
        For xj
            Partition examples by arguments passed to xi (maybe type equivalence classes instead of concrete values)
            Check if for each xi arg part, are all the types passed to xj the same? If they ever vary, remove ji edge

    # Between different functions
    Should help us learn how many variables actually exist, because we assume no fresh vars on RHS
    I have no idea what I want the edges to look like and how we should traverse them to learn things
    Need a new net for each example. Need to duplicate function subgraphs for each application/callsite bc
        instantiations can change for each one
    Consider cycles like between cons and drop
     */

}

/*
If a value is arg to two parameters, there's "flows to" edge to both if we let values be nodes.
Better: Have bidirectional "flows to" edge

Each node has "witnesses" - the types substituted
^^ ok not true bc

Start with dep edge cliques including both directions - 2n^2 edges
 */