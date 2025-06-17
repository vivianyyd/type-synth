package symbolicgen

import query.Example
import query.FlatApp
import query.Query
import query.flatten
import symbolicgen.stc.F
import symbolicgen.stc.SymTypeC
import symbolicgen.stc.Var
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
    private val query: Query, outline: Map<String, SymTypeC>, private val oracle: EqualityNewOracle
) {
    private val nodeToType = outline.entries.fold(mutableMapOf<ParameterNode, SymTypeC>()) { m, (name, tree) ->
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

    fun nodes(name: String) = nodeToType.keys.filter { it.f == name }

    val graphs: Map<String, DependencyGraph> by lazy {
        query.names.associateWith { name ->
            val (deps, loops) = findEdges(name)
            DependencyGraph(name, nodes(name).toSet(), deps, loops)
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

    private fun flatExs(name: String, exs: Collection<Example>) =
        equivalenceClasses(exs.map { it.flatten() }) { e1, e2 -> e1.name == e2.name }.associateBy { it.first().name }[name]
            ?: setOf()

    val all by lazy { query.names.associateWith { findEdges(it) } }

    /** Requires: i is in bounds for ex. */
    private fun arg(ex: FlatApp, i: Int) = if (i == ex.args.size) ex else ex.args[i]

    private fun findEdges(name: String): Triple<Set<DependencyEdge>, Set<SelfLoop>, Set<ParameterNode>> {
        val nodes = nodes(name)
        val deps = mutableSetOf<DependencyEdge>()
        val loops = mutableSetOf<SelfLoop>()
        val mayHaveFresh = mutableSetOf<ParameterNode>()

        // TODO I think we don't actually need all subexprs in posexs here
        val posExs = flatExs(name, query.posExamples)
        val negExs = flatExs(name, query.negExamples)
        val parameters = nodes.filter { it.f == name }

        for (pi in parameters) {
            val i = pi.i

            fun relevantExs(args: Int, exs: Collection<FlatApp>) =
                if (args < nodes.size - 1) exs.filter { it.args.size > args } else exs.filter { it.args.size >= args }

            val pos = relevantExs(i, posExs)
            val neg = relevantExs(i, negExs)

            /** Arguments compatible with this parameter. */
            val args = pos.map { arg(it, i) } // if (i == nodes.size - 1) it else it.args[i]

            if (equivalenceClasses(args, oracle::flatEqual).size == 1) {
                loops.add(SelfLoop(pi))
            }

            /**
             * In each equivalence class, the type of the function that the arg at [argIndex] is applied to is the same
             * */
            fun groupExsByTypeBeforeArg(argIndex: Int, exs: Collection<FlatApp>) =
                equivalenceClasses(exs) { e1, e2 ->
                    oracle.flatEqual(
                        FlatApp(e1.name, e1.args.subList(0, argIndex)),
                        FlatApp(e2.name, e2.args.subList(0, argIndex))
                    )
                    // Weaker test: all args prior to the ith have the same type. Use this if the oracle
                    //   doesn't work for arbitrary subexpressions.. But it should.
//                    e1.args.subList(0, argIndex).zip(e2.args.subList(0, argIndex))
//                        .all { (a1, a2) -> oracle.flatEqual(a1, a2) }
                }

            /**
             * Node p3 has F tag when there exist
             *  + f t1 t2 t3
             *  + f t1 t2 t3'
             * where t3 =/= t3', i.e. there are still degrees of flexibility (unbound variables) in the parameter
             */
            val fTag =
                if (i == nodes.size - 1)
                    false  // No additional arguments to take in, so fully determined. TODO Assumes nullary contains no variables
                else groupExsByTypeBeforeArg(i, pos).any { c ->
                    c.any { e1 ->
                        c.any { e2 -> !oracle.flatEqual(arg(e1, i), arg(e2, i)) }
                    }
                }
            if (fTag) mayHaveFresh.add(pi)

            for (pj in parameters) {
                val j = pj.i
                if (j == i) continue

                fun depEdge(source: Int, sink: Int): Boolean {
                    val posGroupedBySink = equivalenceClasses(relevantExs(max(i, j), pos)) { e1, e2 ->
                        oracle.flatEqual(arg(e1, sink), arg(e2, sink))
                    }
                    val sourceChangesWhileSinkConstant = posGroupedBySink.any { eqClass ->
                        eqClass.any {
                            val arbitraryElem = arg(eqClass.first(), source)
                            !oracle.flatEqual(arg(it, source), arbitraryElem)
                        }
                    }
                    return !sourceChangesWhileSinkConstant
                }
                if (depEdge(i, j)) {
                    deps.add(DependencyEdge(pi, pj))
                }
            }
        }
        return Triple(deps, loops, mayHaveFresh)
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