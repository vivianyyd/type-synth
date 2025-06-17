package constraints

import DependencyAnalysis
import stc.F
import stc.L
import stc.SymTypeC
import stc.Var
import std.flatten
import util.DependencyEdge
import util.ParameterNode
import util.PyWriter
import util.SelfLoop

class LabelConstraintGenerator(
    private val hyp: Map<String, SymTypeC>,
    private val dep: DependencyAnalysis
) {
    private val w = PyWriter()
    private val pyName = mutableMapOf<String, String>()

    init {
        w.comment("$hyp")
        w.import("cvc5.pythonic")
        w.import("cardinality")
        w.beginMain()

        var pyNameFresh = 0
        hyp.keys.forEach { name ->
            val n = "_${name.filter { it.isLetterOrDigit() }}"
            if (n !in pyName.values) pyName[name] = n
            else pyName[name] = n + "_${pyNameFresh++}"
        }
    }

    fun pyParamToNode(p: String) = ParameterNode(
        pyName.entries.find { it.value == p.removePrefix("p").substringBeforeLast('_') }!!.key,
        p.substringAfterLast('_').toInt()
    )

    fun pySizeToL(s: String) = std.L.toL(s.removePrefix("size")).flatten()

    fun pyVarToIds(s: String) = std.Var.toIds(s.removePrefix("v"))

    fun py(node: ParameterNode) = "p${pyName[node.f]!!}_${node.i}"
    private fun py(v: Var) = "v$v"
    private fun pySize(l: L) = "size$l"

    private fun declareInts(names: List<String>) {
        if (names.isEmpty()) return
        val py = names.joinToString(separator = ", ")
        val cvc5 = names.joinToString(separator = " ")
        w.decls(listOf("$py = Int${if (names.size == 1) "" else "s"}('$cvc5')"))
    }

    fun gen(): String {
        val nodeToType = hyp.entries.fold(mutableMapOf<ParameterNode, SymTypeC>()) { m, (name, tree) ->
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

        // Declare top-level variables, label sizes
        val vars = nodeToType.values.filterIsInstance<Var>().map { py(it) }.toSet().toList()
        val lsizes = nodeToType.values.filterIsInstance<L>().map { pySize(it) }.toSet().toList()
        declareInts(vars)
        declareInts(lsizes)

        val varsDistinct = vars.flatMapIndexed { i, u ->
            vars.mapIndexedNotNull { j, v ->
                if (u == v || i < j) null else "$u != $v"
            }
        }

        val labelsMatchConstrs = nodeToType.filter { (_, t) -> t is L }.map { (n, t) ->
            "${pySize(t as L)} >= Cardinality(${py(n)})"
        }

        val varsAreSingletons = nodeToType.filter { (_, t) -> t is Var }.map { (n, t) ->
            "${py(n)} == Singleton(${py(t as Var)})"
        }

        w.constrs(varsDistinct + labelsMatchConstrs + varsAreSingletons)

        // Translate dependency info into set constraints
        dep.all.forEach { (name, info) ->
            val nodes = dep.nodes(name)
            w.decls(nodes.map { "${py(it)} = Const('${py(it)}', SetSort(IntSort()))" })

            val (deps, primitives, fresh) = info
            val edgeConstrs = nodes.map {
                if (SelfLoop(it) in primitives) "${py(it)} == EmptySet(IntSort())"
                else "${py(it)} != EmptySet(IntSort())"
            } + nodes.flatMap { p1 ->
                nodes.mapNotNull { p2 ->
                    if (p1.i < p2.i) {
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
//                    val rel = if (p in fresh) "!=" else "=="
                    val empty = "EmptySet(IntSort())"
                    if (p !in fresh) "$diffPrev == $empty" else null
                }
            }
            w.constrs(edgeConstrs + freshConstrs)
        }

        return w.s()
    }
}