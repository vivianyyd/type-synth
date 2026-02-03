package core

import core.languages.*
import dependencyanalysis.ParameterNode
import dependencyanalysis.ParameterwiseDependencyAnalysis
import util.PyWriter

class NewLabelArityConstraints(
    private val cand: Candidate<Elaborated>,
    private val dep: ParameterwiseDependencyAnalysis
) {

    private val pyName = mutableMapOf<String, String>()
    private val decls = mutableListOf<String>()
    private val constrs = mutableListOf<String>()

    init {
        var pyNameFresh = 0
        cand.names.forEach { name ->
            val n = "_${name.filter { it.isLetterOrDigit() }}"
            if (n !in pyName.values) pyName[name] = n else pyName[name] = n + "_${pyNameFresh++}"
        }

        val nodeToType =
            cand.names.zip(cand.types).fold(
                mutableMapOf<ParameterNode, SearchNode<Elaborated>>()
            ) { m, (name, tree) ->
                var curr = tree
                var count = 0
                while (curr is NArrow) {
                    m[ParameterNode(name, count)] = curr.l
                    count++
                    curr = curr.r
                }
                m[ParameterNode(name, count)] = curr
                m
            }

        // Declare top-level variables, label sizes
        val vars = nodeToType.values.filterIsInstance<ElaboratedV>().map { py(it) }.toSet().toList()
        //        TODO("need to look inside functions for labels")
        val lsizes =
            nodeToType.values.filterIsInstance<ElaboratedL>().map { pySize(it) }.toSet().toList()
        declareInts(vars)
        declareInts(lsizes)

        val varsDistinct =
            vars.flatMapIndexed { i, u ->
                vars.mapIndexedNotNull { j, v -> if (u == v || i < j) null else "$u != $v" }
            }

        val labelsMatchConstrs =
            nodeToType
                .filter { (_, t) -> t is ElaboratedL }
                .map { (n, t) -> "${pySize(t as ElaboratedL)} >= Cardinality(${py(n)})" }

        val varsAreSingletons =
            nodeToType
                .filter { (_, t) -> t is ElaboratedV }
                .map { (n, t) -> "${py(n)} == Singleton(${py(t as ElaboratedV)})" }

        constrs.addAll(varsDistinct + labelsMatchConstrs + varsAreSingletons)

        /** Union parameters [0 to n) */
        fun union(name: String, n: Int): String {
            require(n > 0)
            return if (n == 1) py(ParameterNode(name, 0))
            else "SetUnion(${union(name, n - 1)}, ${py(ParameterNode(name, n - 1))})"
        }

        cand.names.forEach { name ->
            val nodes = dep.nodes(name)
            decls.addAll(nodes.map { "${py(it)} = Const('${py(it)}', SetSort(IntSort()))" })
        }

        // Translate dependency info into set constraints
        val fixedConstrs =
            dep.fixed.flatMap { (name, a) ->
                // if fixed, vars for this param are a subset of union of previous ones
                a.mapIndexedNotNull { i, fixed ->
                    if (fixed && i > 0) {
                        "IsSubset(${py(ParameterNode(name, i))}, ${union(name, i)})"
                    } else null
                }
            }
        val constrainedConstrs =
            dep.constrained.flatMap { (name, a) ->
                a.mapIndexedNotNull { i, constrained ->
                    if (constrained && i > 0) {
                        "SetIntersect(${py(ParameterNode(name, i))}, ${union(name, i)}) != EmptySet(IntSort())"
                    } else null // TODO not sure if we can introduce an == constraint in this case
                }
            }
        constrs.addAll(fixedConstrs + constrainedConstrs)
    }

    fun pyParamToNode(p: String) =
        ParameterNode(
            pyName.entries.find { it.value == p.removePrefix("p").substringBeforeLast('_') }!!.key,
            p.substringAfterLast('_').toInt()
        )

    fun pySizeToL(s: String) = ElaboratedL.fromString(s.removePrefix("size"))

    fun pyVarToIds(s: String) = products.std.Var.toIds(s.removePrefix("v"))

    fun py(node: ParameterNode) = "p${pyName[node.f]!!}_${node.i}"

    private fun py(v: ElaboratedV) = "$v"

    private fun pySize(l: ElaboratedL) = "size$l"

    private fun declareInts(names: List<String>) {
        if (names.isEmpty()) return
        val py = names.joinToString(separator = ", ")
        val cvc5 = names.joinToString(separator = " ")
        decls.add("$py = Int${if (names.size == 1) "" else "s"}('$cvc5')")
    }

    fun initialQuery(): String = PyWriter().query("${cand.asMap}", decls, constrs)

    fun smallerQuery(sizes: Map<Int, Int>): String {
        fun or(args: List<String>): String {
            if (args.size == 1) return args.single()
            return "Or(${args.first()},${or(args.drop(1))})"
        }
        constrs.add(or(sizes.entries.map { "${pySize(ElaboratedL(it.key))} < ${it.value}" }))
        return PyWriter().query("$cand", decls, constrs)
    }
}
