package dependencyanalysis

import query.Example
import query.Examples
import query.FlatApp
import util.Oracle
import util.equivalenceClasses
import java.lang.Integer.max

class ArrowDependencyAnalysis(
    private val examples: Examples,
    arities: Map<String, Int>,
    private val oracle: Oracle
) {
    private val nodes =
        arities.flatMap { (name, arity) -> (0 until arity).map { ParameterNode(name, it) } }

    fun nodes(name: String) = nodes.filter { it.f == name }

    val graphs: Map<String, ArrowDependencyGraph> by lazy {
        examples.names.associateWith { name ->
            val (deps, loops) = findEdges(name)
            ArrowDependencyGraph(name, nodes(name).toSet(), deps, loops)
        }
    }

    private fun flatExs(name: String, exs: Collection<Example>) =
        equivalenceClasses(exs.map { it.flatten() }) { e1, e2 -> e1.name == e2.name }
            .associateBy { it.first().name }[name] ?: setOf()

    val all by lazy { examples.names.associateWith { findEdges(it) } }

    fun mayHaveFresh(name: String, param: Int) = mayHaveFresh(ParameterNode(name, param))

    fun mayHaveFresh(p: ParameterNode) = p in all[p.f]!!.third

    /** Requires: i is in bounds for ex. */
    private fun arg(ex: FlatApp, i: Int) = if (i == ex.args.size) ex else ex.args[i]

    private fun findEdges(
        name: String
    ): Triple<Set<DependencyEdge>, Set<SelfLoop>, Set<ParameterNode>> {
        val nodes = nodes(name)
        val deps = mutableSetOf<DependencyEdge>()
        val loops = mutableSetOf<SelfLoop>()
        val mayHaveFresh = mutableSetOf<ParameterNode>()

        val posExs = flatExs(name, examples.posWithSubexprs)
        val negExs = flatExs(name, examples.neg)
        val parameters = nodes.filter { it.f == name }

        for (pi in parameters) {
            val i = pi.i

            fun relevantExs(paramIndex: Int, exs: Collection<FlatApp>) =
                if (paramIndex < nodes.size - 1)
                    exs.filter { it.args.size > paramIndex && it.args.size < nodes.size }
                else exs.filter { it.args.size == paramIndex }

            val pos = relevantExs(i, posExs)
            val neg = relevantExs(i, negExs)

            /** Arguments compatible with this parameter. */
            val args = pos.map { arg(it, i) } // if (i == nodes.size - 1) it else it.args[i]

            if (equivalenceClasses(args, oracle::flatEqual).size == 1) {
                loops.add(SelfLoop(pi))
            }

            /**
             * In each equivalence class, the type of the function that the arg at [argIndex] is
             * applied to is the same
             */
            fun groupExsByTypeBeforeArg(argIndex: Int, exs: Collection<FlatApp>) =
                equivalenceClasses(exs) { e1, e2 ->
                    oracle.flatEqual(
                        FlatApp(e1.name, e1.args.subList(0, argIndex)),
                        FlatApp(e2.name, e2.args.subList(0, argIndex))
                    )
                    // Weaker test: all args prior to the ith have the same type. Use this if the
                    // oracle
                    //   doesn't work for arbitrary subexpressions.. But it should.
                    //                    e1.args.subList(0, argIndex).zip(e2.args.subList(0,
                    // argIndex))
                    //                        .all { (a1, a2) -> oracle.flatEqual(a1, a2) }
                }

            /**
             * Node p3 has F tag when there exist
             * + f t1 t2 t3
             * + f t1 t2 t3' where t3 =/= t3', i.e. there are still degrees of flexibility (unbound
             *   variables) in the parameter
             */
            val fTag =
                if (i == nodes.size - 1)
                    false // No additional arguments to take in, so fully determined. TODO Assumes
                // nullary contains no variables
                else
                    groupExsByTypeBeforeArg(i, pos).any { c ->
                        c.any { e1 -> c.any { e2 -> !oracle.flatEqual(arg(e1, i), arg(e2, i)) } }
                    }
            if (fTag) mayHaveFresh.add(pi)

            for (pj in parameters) {
                val j = pj.i
                if (j == i) continue

                fun depEdge(source: Int, sink: Int): Boolean {
                    val posGroupedBySink =
                        equivalenceClasses(relevantExs(max(i, j), pos)) { e1, e2 ->
                            oracle.flatEqual(arg(e1, sink), arg(e2, sink))
                        }
                    val sourceChangesWhileSinkConstant =
                        posGroupedBySink.any { eqClass ->
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
