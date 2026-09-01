package oneast

import dependencyanalysis.ParameterNode
import dependencyanalysis.ParameterwiseDependencyAnalysis
import util.PyWriter
import util.io.cvc.CVCParser
import util.io.cvc.callCVC
import util.io.cvc.readCVC
import util.lines

class LabelConstraints(
    private val s: SearchState,
    private val dep: ParameterwiseDependencyAnalysis,
    preserveValues: Boolean
) {

    private val nameToPy = mutableMapOf<String, String>()
    private val decls = mutableListOf<String>()
    private val constrs = mutableListOf<String>()

    init {
        var fresh = 0
        s.names.keys.forEach { name ->
            val stripped = "_${name.filter { it.isLetterOrDigit() }}"
            if (stripped !in nameToPy.values) nameToPy[name] = stripped
            else nameToPy[name] = stripped + "_${fresh++}"
        }

        val paramToType =
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

        /*
        Declare parameters, and top-level variables and label sizes.
        - Each parameter corresponds to a set that represents the variables that appear in it.
          We use Int sets since there are arbitrarily many Ints
        - Each unique variable corresponds to a unique Int that may be an element of a set.
        - Each unique label corresponds to a label size, which is an integer.
        Note that we only analyze the variables and labels that occur at the top-level.
         */
        s.names.keys.forEach { name ->
            val nodes = dep.nodes(name)
            decls.addAll(nodes.map { "${py(it)} = Const('${py(it)}', SetSort(IntSort()))" })
        }
        val vars = paramToType.values.filterIsInstance<Variable>().map { py(it) }.toSet().toList()
        val lsizes =
            paramToType.values.filterIsInstance<NamedLabel>().map { pySize(it) }.toSet().toList()
        declareInts(vars)
        declareInts(lsizes)

        // Committed label arities are always pinned. Non-committed existing arities are pinned only
        // when [preserveValues] is true.
        s.labelArities.forEach { (label, arity) ->
            if (label in s.committedLabels || preserveValues) {
                constrs.add("${pySize(label)} == $arity")
            }
        }

        // All distinct variables must correspond to unique elements in a set
        val varsDistinct =
            vars.flatMapIndexed { i, u ->
                vars.mapIndexedNotNull { j, v -> if (u == v || i < j) null else "$u != $v" }
            }

        // This assumption leads us to overestimate label arities sometimes:
        // Each label size must be at least the cardinality of each parameter for which that label
        // appears at the top-level.
        // It is an overestimation because consider a function that returns a list of pairs. The
        // output parameter must contain two variables, and therefore has cardinality 2. But the
        // list label actually can still have size 1.
        val labelsMatchConstrs =
            paramToType
                .filter { (_, t) -> t is NamedLabel }
                .map { (n, t) -> "${pySize(t as NamedLabel)} >= Cardinality(${py(n)})" }

        // When a variable appears as a top-level parameter, that parameter is a singleton set.
        val varsAreSingletons =
            paramToType
                .filter { (_, t) -> t is Variable }
                .map { (n, t) -> "${py(n)} == Singleton(${py(t as Variable)})" }

        constrs.addAll(varsDistinct + labelsMatchConstrs + varsAreSingletons)

        // Translate dependency info into set constraints
        // If a parameter is fixed, its variables are a subset of the union of previous parameters
        val fixedConstrs =
            dep.fixed.flatMap { (name, fixedParams) ->
                fixedParams.mapIndexedNotNull { i, fixed ->
                    if (fixed && i > 0) {
                        "IsSubset(${py(ParameterNode(name, i))}, ${union(name, i)})"
                    } else null
                }
            }
        // If a parameter is constrained, it has nonempty intersection with union of previous
        // parameters
        val constrainedConstrs =
            dep.constrained.flatMap { (name, a) ->
                a.mapIndexedNotNull { i, constrained ->
                    if (constrained && i > 0) {
                        TODO("This is wrong. something can be negex if there's a label mismatch, might" +
                                "have nothing to do with label parameters." +
                                "We should update constrained to take this into account - " +
                                "under our hyp with label names but not label holes (?? think??), the labels match i.e. we accept" +
                                "but it's a negex. we can't just omit this check, or we'll just think everything is 0" +
                                "Dep analysis actually needs to be performed for every outline" +
                                "This forces us to believe smaller label arities assignments are unsat when they are ok." +
                                "While previously this was not a problem because we iteratively deepen up to a bound," +
                                "Now it matters because we impose the additional constraint that solns must match" +
                                "committed labels. But this is not possible if we erroneously think that committed label" +
                                "arity is unsat")
                        "SetIntersect(${py(ParameterNode(name, i))}, ${union(name, i)}) != EmptySet(IntSort())"
                    } else null // TODO not sure if we can introduce an == constraint in this case
                }
            }
        constrs.addAll(fixedConstrs + constrainedConstrs)

        // TODO CVC query needs to ask whether it's SAT to carry over leq prev label arities and
        //   still satisfy dep constraints on new ones.
        //   If UNSAT, we need to resolve for arities of all labels that appear in types that
        //   contain holes. Update labelArities and SearchState types.
        s.labelArities.entries.forEach {}
    }

    fun pyParamToNode(p: String) =
        ParameterNode(
            nameToPy.entries
                .find { it.value == p.removePrefix("p").substringBeforeLast('_') }!!
                .key,
            p.substringAfterLast('_').toInt()
        )

    /** Union parameters [0 to [n]) of [name]. */
    fun union(name: String, n: Int): String {
        require(n > 0)
        return if (n == 1) py(ParameterNode(name, 0))
        else "SetUnion(${union(name, n - 1)}, ${py(ParameterNode(name, n - 1))})"
    }

    private fun py(node: ParameterNode) = "p${nameToPy[node.f]!!}_${node.i}"

    private fun py(v: Variable) = "$v"

    private fun pySize(l: Int) = "size$l"

    private fun pySize(l: NamedLabel) = pySize(l.label)

    private fun pySizeToLabel(s: String) = s.removePrefix("size").toInt()

    private fun declareInts(names: List<String>) {
        if (names.isEmpty()) return
        val py = names.joinToString(separator = ", ")
        val cvc5 = names.joinToString(separator = " ")
        decls.add("$py = Int${if (names.size == 1) "" else "s"}('$cvc5')")
    }

    private val header = "\"\"\"\n" +
            s.asMap().entries.partition { it.value is Arrow }.let { (fns, nullaries) -> nullaries + fns }.lines() +
            "\n===\n" +
            nameToPy +
            "\n\"\"\""

    private fun makeQuery(): String = PyWriter().query(header, decls, constrs)

    fun initialQuery(): String = makeQuery()

    private fun smallerQuery(sizes: Map<Int, Int>): String {
        fun or(args: List<String>): String {
            if (args.size == 1) return args.single()
            return "Or(${args.first()},${or(args.drop(1))})"
        }
        constrs.add(or(sizes.entries.map { "${pySize(it.key)} < ${it.value}" }))
        return makeQuery()
    }

    fun smallerQuery(p: CVCParser): String = smallerQuery(extract(p))

    fun extract(p: CVCParser) = p.sizes.mapKeys { pySizeToLabel(it.key) }
}

fun labelArities(s: SearchState, deps: ParameterwiseDependencyAnalysis): Map<Int, Int>? {
    /**
     * @param [preserveValues] Whether to keep or override existing label arities.
     */
    fun attempt(preserveValues: Boolean): Map<Int, Int>? {
        val gen = LabelConstraints(s, deps, preserveValues)
        val testID = "${s.id}"
        callCVC(gen.initialQuery(), testID)

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
    // Start by trying to preserve existing arities. If fail, try again with overwriting
    // TODO. AllMinSAT, and we should also do both with and without preserving arities
    //       rather than only allowing overwriting if preserving fails.
    //       i.e. There might be a better soln that does not preserve old arities.
    //       If later we iteratively deepen labels anyway, is the latter necessary?
    //       Could we guarantee if when we add more examples arities only get bigger?
    //       Bc they could only show off more flexibility
    return attempt(s.labelArities.isNotEmpty()) ?: attempt(false)
}
