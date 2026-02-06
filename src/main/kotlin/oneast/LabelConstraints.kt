package oneast

import dependencyanalysis.ParameterNode
import dependencyanalysis.ParameterwiseDependencyAnalysis
import util.PyWriter
import util.io.cvc.CVCParser
import util.io.cvc.callCVC
import util.io.cvc.readCVC

class LabelConstraints(
    private val s: SearchState,
    private val dep: ParameterwiseDependencyAnalysis
) {

    private val pyName = mutableMapOf<String, String>()
    private val decls = mutableListOf<String>()
    private val constrs = mutableListOf<String>()

    init {
        var pyNameFresh = 0
        s.names.keys.forEach { name ->
            val n = "_${name.filter { it.isLetterOrDigit() }}"
            if (n !in pyName.values) pyName[name] = n else pyName[name] = n + "_${pyNameFresh++}"
        }

        val nodeToType =
            s.names.entries.fold(mutableMapOf<ParameterNode, Type>()) { m, (name, index) ->
                val tree = s.types[index]
                var curr = tree
                var count = 0
                while (curr is Arrow) {
                    m[ParameterNode(name, count)] = curr.l
                    count++
                    curr = curr.r
                }
                m[ParameterNode(name, count)] = curr
                m
            }

        // Declare top-level variables, label sizes
        val vars = nodeToType.values.filterIsInstance<Variable>().map { py(it) }.toSet().toList()
        //        TODO("need to look inside functions for labels")
        val lsizes =
            nodeToType.values.filterIsInstance<NamedLabel>().map { pySize(it) }.toSet().toList()
        declareInts(vars)
        declareInts(lsizes)

        val varsDistinct =
            vars.flatMapIndexed { i, u ->
                vars.mapIndexedNotNull { j, v -> if (u == v || i < j) null else "$u != $v" }
            }

        val labelsMatchConstrs =
            nodeToType
                .filter { (_, t) -> t is NamedLabel }
                .map { (n, t) -> "${pySize(t as NamedLabel)} >= Cardinality(${py(n)})" }

        val varsAreSingletons =
            nodeToType
                .filter { (_, t) -> t is Variable }
                .map { (n, t) -> "${py(n)} == Singleton(${py(t as Variable)})" }

        constrs.addAll(varsDistinct + labelsMatchConstrs + varsAreSingletons)

        /** Union parameters [0 to n) */
        fun union(name: String, n: Int): String {
            require(n > 0)
            return if (n == 1) py(ParameterNode(name, 0))
            else "SetUnion(${union(name, n - 1)}, ${py(ParameterNode(name, n - 1))})"
        }

        s.names.keys.forEach { name ->
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

    fun py(node: ParameterNode) = "p${pyName[node.f]!!}_${node.i}"

    private fun py(v: Variable) = "$v"

    private fun pySize(l: Int) = "size$l"

    private fun pySize(l: NamedLabel) = pySize(l.label)

    fun pySizeToLabel(s: String) = s.removePrefix("size").toInt()

    private fun declareInts(names: List<String>) {
        if (names.isEmpty()) return
        val py = names.joinToString(separator = ", ")
        val cvc5 = names.joinToString(separator = " ")
        decls.add("$py = Int${if (names.size == 1) "" else "s"}('$cvc5')")
    }

    fun initialQuery(): String = PyWriter().query("${s.asMap()}", decls, constrs)

    private fun smallerQuery(sizes: Map<Int, Int>): String {
        fun or(args: List<String>): String {
            if (args.size == 1) return args.single()
            return "Or(${args.first()},${or(args.drop(1))})"
        }
        constrs.add(or(sizes.entries.map { "${pySize(it.key)} < ${it.value}" }))
        return PyWriter().query("$s", decls, constrs)
    }

    fun smallerQuery(p: CVCParser): String = smallerQuery(extract(p))

    fun extract(p: CVCParser) = p.sizes.mapKeys { pySizeToLabel(it.key) }
}

fun labelArities(
    s: SearchState,
    deps: ParameterwiseDependencyAnalysis,
    callSolver: Boolean
): Map<Int, Int>? {
    val gen = LabelConstraints(s, deps)
    val testID = "${s.id}"
    if (callSolver) callCVC(gen.initialQuery(), testID)

    var counter = 0
    var previousSolution = readCVC(testID) ?: return null
    var lastSuccessful = -1
    do {
        val parser = CVCParser(previousSolution)
        val testName = "$testID-smaller${counter++}"
        val cont =
            if (parser.sizes.isNotEmpty()) callCVC(gen.smallerQuery(parser), testName) else false
        if (cont) {
            lastSuccessful = counter - 1
            previousSolution = readCVC(testName)!! // callCVC returns success code stored in cont
        }
    } while (cont)
    val finalSuccessfulOutput =
        if (lastSuccessful == -1) testID else "$testID-smaller$lastSuccessful"

    return gen.extract(CVCParser(readCVC(finalSuccessfulOutput)!!))
}
