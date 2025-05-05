package symbolicgen

import symbolicgen.symbolicenumerator.L
import symbolicgen.symbolicenumerator.Var
import util.DependencyEdge
import util.ParameterNode
import util.PyWriter
import util.SelfLoop

class LabelConstraintGenerator(
    private val dep: DependencyAnalysis
) {
    private val w = PyWriter()
    private val depInfo = dep.all()
    private val pyName = mutableMapOf<String, String>()

    init {
        w.import("cvc5.pythonic")
        w.import("cardinality")
        w.beginMain()

        var pyNameFresh = 0
        depInfo.keys.forEach { name ->
            val n = "_${name.filter { it.isLetterOrDigit() }}"
            if (n !in pyName.values) pyName[n] = n
            else pyName[n] = n + "_${pyNameFresh++}"
        }
    }

    private fun py(node: ParameterNode) = "${pyName[node.f]!!}_${node.i}"

    private fun declareInts(names: List<String>) =
        w.decls(listOf("${names.joinToString(separator = ", ")} = Ints('${names.joinToString(separator = " ")}')"))

    fun gen(): String {
        // Declare top-level variables, label sizes
        val vars = dep.nodeToType.values.filterIsInstance<Var>().map { "v$it" }.toSet().toList()
        val lsizes = dep.nodeToType.values.filterIsInstance<L>().map { "$it" }.toSet().toList()
        declareInts(vars)
        declareInts(lsizes)

        // Translate dependency info into set constraints
        depInfo.forEach { (name, info) ->
            val nodes = dep.nodes(name)
            w.decls(nodes.map { "${py(it)} = Const('${py(it)}', SetSort(IntSort()))" })

            val (deps, primitives, fresh) = info
            val edgeConstrs = nodes.flatMap { p1 ->
                nodes.mapNotNull { p2 ->
                    if (p1.i == p2.i) {
                        if (SelfLoop(p1) in primitives) listOf("${py(p1)} == EmptySet(IntSort())")
                        else listOf("${py(p1)} != EmptySet(IntSort())")
                    } else if (p1.i < p2.i) {
                        val p1subp2 = DependencyEdge(p1, p2) in deps
                        val p2subp1 = DependencyEdge(p2, p1) in deps
                        if (p1subp2 && p2subp1) listOf("${py(p1)} == ${py(p2)}")
                        else {
                            val tmp1 = "IsSubset(${py(p1)}, ${py(p2)})"
                            val tmp2 = "IsSubset(${py(p2)}, ${py(p1)})"
                            listOf(if (p1subp2) tmp1 else "Not($tmp1)", if (p2subp1) tmp2 else "Not($tmp2)")
                        }
                    } else null
                }
            }.flatten()
            w.constrs(edgeConstrs)

            // TODO fresh variable constraints with setminus and union
        }

        // Add constraint: all params with same label must have matched varset sizes
        // Add constraint: all params with variable must be singletons containing that variable (make int literals)
        val paramHypotheses = dep.nodeToType

        return w.s()
    }
}