package enumgen

import util.Application

interface EqualityOracle {
    fun equal(a: Application, b: Application): Boolean
}

data class ParameterNode(val f: String, val i: Int) {
    private var ctr = 0
    fun freshArgument() = ArgumentNode(f, i, ctr++)
}

data class ArgumentNode(val f: String, val i: Int, val id: Int)

sealed interface Edge

/** directed, variables subset relation */
data class DependencyEdge(val sub: ParameterNode, val sup: ParameterNode) : Edge
// TODO is it weird that this is a data class but [LinkEdge] isn't?

/** undirected, otherwise nonempty intersection */
class LinkEdge(val a: ParameterNode, val b: ParameterNode) : Edge

// TODO decide if nodes/edges should be constructed in init block or by DepAnalysis class and only stored here
class DependencyGraph(
    val name: String,
    val nodes: Set<ParameterNode>,
    val links: Set<LinkEdge>,
    val deps: Set<DependencyEdge>
) {
    /**
     * Invariants: all [f] fields of contained nodes are the same. All edges only contain those nodes
     */
    val edges: Set<Edge> by lazy { links + deps }
}

class ExampleNet {

}

fun equals(p1: ParameterNode, p2: ParameterNode): Boolean =
    TODO(
        "Does this even make sense? The runtime value " +
                "of a parameter type depends on previous arguments. " +
                "Also, output parameters are weird bc we can't substitute into them."
    )

data class TypeEquivalenceClassDummy(val id: Int)

/*
 * TODO:
 *  Inputs are functions and arities (manually write for now, then write analysis for this)
 *  Visualizer for dep graphs
 */
class DependencyAnalysis(
    private val names: List<String>,
    private val posExamples: Set<Application>,
    private val negExamples: Set<Application>,
    private val oracle: EqualityOracle
) {
    var dummyCounter = 0
    val dummyTypes: Map<Application, TypeEquivalenceClassDummy> by lazy {
        val m = mutableMapOf<Application, TypeEquivalenceClassDummy>()
        posExamples.forEach {ex ->
            fun rec(a: Application) {
                m.forEach { (b, dummy) ->
                    if (oracle.equal(a, b)) m[a] = dummy
                    else m[a] = TypeEquivalenceClassDummy(dummyCounter++)
                }
                a.arguments?.forEach { rec(it) }
            }
            rec(ex)
        }
        m
    }

    val uniqueTypes: Set<TypeEquivalenceClassDummy> = dummyTypes.values.toSet()

    val exampleAnalysis = ExampleAnalysis(names, posExamples, negExamples)  // todo seems like bad modularity
    val nodes: Set<ParameterNode> = exampleAnalysis.params.entries.fold(setOf()) { acc, (name, numParams) ->
        acc.union((1..numParams).map { ParameterNode(name, it) }.toSet())
    }

    val graphs: Map<String, DependencyGraph> by lazy {
        names.associateWith { name ->
            DependencyGraph(name, nodes.filter { it.f == name }.toSet(), findLinks(name), findDeps(name))
        }
    }

    private fun findLinks(name: String): Set<LinkEdge> = TODO("Think about algo to do deps and links simulataneously")
    private fun findDeps(name: String): Set<DependencyEdge> = TODO()
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
            Check if for each xi arg part, are all the types passed to xj the same? If they ever vary, remove ij edge


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