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
            if (n !in pyName.values) pyName[name] = n
            else pyName[name] = n + "_${pyNameFresh++}"
        }
    }

    private fun py(node: ParameterNode) = "${pyName[node.f]!!}_${node.i}"
    private fun py(v: Var) = "v$v"
    private fun pySize(l: L) = "$l"

    private fun declareInts(names: List<String>) {
        if (names.isEmpty()) return
        val py = names.joinToString(separator = ", ")
        val cvc5 = names.joinToString(separator = " ")
        w.decls(listOf("$py = Int${if (names.size == 1) "" else "s"}('$cvc5')"))
    }

    fun gen(): String {
        // Declare top-level variables, label sizes
        val vars = dep.nodeToType.values.filterIsInstance<Var>().map { py(it) }.toSet().toList()
        val lsizes = dep.nodeToType.values.filterIsInstance<L>().map { pySize(it) }.toSet().toList()
        declareInts(vars)
        declareInts(lsizes)
        val labelsMatchConstrs = dep.nodeToType.filter { (_, t) -> t is L }.map { (n, t) ->
            "${pySize(t as L)} >= Cardinality(${py(n)})"
        }

        val varsAreSingletons = dep.nodeToType.filter { (_, t) -> t is Var }.map { (n, t) ->
            "${py(n)} == Singleton(${py(t as Var)})"
        }

        w.constrs(labelsMatchConstrs + varsAreSingletons)

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

            val freshConstrs = nodes.mapNotNull { p ->
                if (p.i == 0) null
                else {
                    /** Union parameters [0 to n) */
                    fun union(n: Int): String {
                        return if (n == 1) py(ParameterNode(p.f, 0))
                        else "SetUnion(${union(n - 1)}, ${py(ParameterNode(p.f, n - 1))})"
                    }

                    val diffPrev = "SetMinus(${py(p)}, ${union(p.i)})"
                    val rel = if (p in fresh) "!=" else "=="
                    val empty = "EmptySet(IntSort())"
                    "$diffPrev $rel $empty"
                }
            }
            w.constrs(edgeConstrs + freshConstrs)
        }

        return w.s()
    }
}