package enumgen

import enumgen.visualizations.SearchStateVisualizer
import util.Application
import util.equivalenceClasses
import java.lang.Integer.max

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
class LinkEdge(val a: ParameterNode, val b: ParameterNode) : Edge {
    override fun equals(other: Any?): Boolean {
        if (other !is LinkEdge) return false
        return (a == other.a && b == other.b) || (a == other.b && b == other.a)
    }

    override fun hashCode(): Int {
        return a.hashCode() + b.hashCode()  // TODO aaa
    }
}

/** TODO maybe these should just be a type of dependency */
class SelfLoop(val a: ParameterNode) : Edge

// TODO decide if nodes/edges should be constructed in init block or by DepAnalysis class and only stored here
class DependencyGraph(
    val name: String,
    val nodes: Set<ParameterNode>,
    val links: Set<LinkEdge>,
    val deps: Set<DependencyEdge>,
    val loops: Set<SelfLoop>
) {
    /**
     * Invariants: all [f] fields of contained nodes are the same. All edges only contain those nodes
     */
    val edges: Set<Edge> by lazy { links + deps + loops }
}

class ExampleNet {

}

fun equals(p1: ParameterNode, p2: ParameterNode): Boolean =
    TODO(
        "Does this even make sense? The runtime value " +
                "of a parameter type depends on previous arguments. " +
                "Also, output parameters are weird bc we can't substitute into them."
    )

//data class TypeEquivalenceClassDummy(val id: Int)

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
    // TODO maybe the oracle should support this, but then it would have access to all the examples which is not good
    //  encapsulation compared to taking requests and memoizing them. But this approach is the same thing using 2x space
//    var dummyCounter = 0
//    val dummyTypes: Map<Application, TypeEquivalenceClassDummy> by lazy {
//        val m = mutableMapOf<Application, TypeEquivalenceClassDummy>()
//        posExamples.forEach { ex ->
//            fun rec(a: Application) {
//                m.forEach { (b, dummy) ->
//                    if (oracle.equal(a, b)) m[a] = dummy
//                    else m[a] = TypeEquivalenceClassDummy(dummyCounter++)
//                }
//                a.arguments?.forEach { rec(it) }
//            }
//            rec(ex)
//        }
//        m
//    }
//
//    val uniqueTypes: Set<TypeEquivalenceClassDummy> = dummyTypes.values.toSet()

    val exampleAnalysis = ExampleAnalysis(names, posExamples, negExamples)  // todo seems like bad modularity
    val nodes: Set<ParameterNode> = names.fold(setOf()) { acc, name ->
        acc.union((0 until exampleAnalysis.params(name)).map { ParameterNode(name, it) }.toSet())
    }

    val graphs: Map<String, DependencyGraph> by lazy {
        names.associateWith { name ->
            val (links, deps, loops) = findEdges(name)
            DependencyGraph(name, nodes.filter { it.f == name }.toSet(), links, deps, loops)
        }
    }

    /** Precondition: i is in bounds */
    fun Application.getParam(i: Int) =
        if (i < this.arguments!!.size) this.arguments[i]
        else {
            assert(i == this.arguments.size)
            this
        }

    private fun findEdges(name: String): Triple<Set<LinkEdge>, Set<DependencyEdge>, Set<SelfLoop>> {
        val links = mutableSetOf<LinkEdge>()
        val deps = mutableSetOf<DependencyEdge>()
        val loops = mutableSetOf<SelfLoop>()

        val posExs = exampleAnalysis.posFor(name)
        val negExs = exampleAnalysis.negFor(name)
        val parameters = nodes.filter { it.f == name }
        for (pi in parameters) {
            for (pj in parameters) {
                val i = pi.i
                val j = pj.i

                // Skip half the pairs since links are undirected. We'll do both directions of deps at once below
                if (j < i) continue

                // We wait til now to do this filtering so we can use as many exs as possible, since sometimes it might
                //  be only partially applied. At the cost of extra work
                val pos = if (exampleAnalysis.params(name) == 1) posExs
                else posExs.filter { it.arguments != null && it.arguments.size >= max(i, j) }
                val neg = if (exampleAnalysis.params(name) == 1) negExs
                else negExs.filter { it.arguments != null && it.arguments.size >= max(i, j) }

                if (i == j) {
                    if (equivalenceClasses(pos) { e1, e2 ->
                            oracle.equal(e1.getParam(i), e2.getParam(i))
                        }.size == 1) loops.add(SelfLoop(pi))
                } else {
                    // Do both directions of dependency edges
                    fun depEdge(source: Int, sink: Int): Boolean {
                        val groupedBySink =
                            equivalenceClasses(pos) { e1, e2 -> oracle.equal(e1.getParam(sink), e2.getParam(sink)) }
                        val sourceChangesWhileSinkConstant =
                            groupedBySink.any { eqClass ->
                                eqClass.any {
                                    !oracle.equal(it.getParam(source), eqClass.first().getParam(source))
                                }
                            }
                        return !sourceChangesWhileSinkConstant
                    }

                    var depEdge = false
                    if (depEdge(i, j)) {
                        depEdge = true
                        deps.add(DependencyEdge(pi, pj))
                    }
                    if (depEdge(j, i)) {
                        depEdge = true
                        deps.add(DependencyEdge(pj, pi))
                    }

                    // Dependencies are strictly more informative than links, so only add links if we failed before
                    // TODO nicer way?
                    if (!depEdge) {
                        neg.forEach { ne ->
                            val ai = ne.getParam(i)
                            val aj = ne.getParam(j)

                            if (pos.any { pe -> oracle.equal(pe.getParam(i), ai) } &&
                                pos.any { pe -> oracle.equal(pe.getParam(j), aj) }) links.add(LinkEdge(pi, pj))
                        }
                    }
                }
            }
        }
        return Triple(links, deps, loops)
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