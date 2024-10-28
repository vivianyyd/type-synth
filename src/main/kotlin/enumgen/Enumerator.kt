package enumgen

/**
 * If [arguments] is null, the function [name] is not applied.
 *
 * Later: If [arguments] is empty, [name] is applied with no arguments. For now, unit doesn't exist, all fn must have an
 * argument to be applied, this is WLOG since we can just have a unit value be passed
 */
data class Application(val name: String, val arguments: List<Application>?)

typealias Assignment = MutableMap<String, Type>

class Enumerator(
    private val names: List<String>,
    private val posExamples: Set<Application>,
    private val MAX_TYPE_PARAMS: Int
) {
    // TODO("Assert that [posExamples] only contains names in [names]")
    private val u = Unify()  // TODO make this less dumb
    private val searchTree = SearchTree(names)

    private val labels = listOf("l0", "l1", "l2")

    private var varCounter = 0
    private fun freshVariable() =  // alph for readability
        Variable("${if (varCounter++ in 0..25) (varCounter + 96).toChar() else varCounter}")

    private fun typeExpansion() =
        listOf(Function(TypeHole(), TypeHole())) +
                freshVariable() +
                labels.map { lbl ->
                    (0..MAX_TYPE_PARAMS).map { numParams ->
                        LabelNode(lbl, List(numParams) { TypeHole() })
                    }
                }

    private fun fillAll(nodes: List<SearchNode>): Boolean {
        return nodes.fold(false) { acc, node -> fill(node) || acc }
    }

    /**
     * Fill one shallowest child hole in [tree].
     * Returns true if a change was made.
     */
    private fun fill(tree: SearchNode): Boolean {
        when (tree) {
            is Hole -> throw Exception("Parent should've filled this")
            is LangNode -> TODO()
            is VariableNode -> return false
            is ArrowNode -> {
                var flag = false
                tree.left.map {
                    // TODO expand all children. but wait, my rep is wrong
                }
                val l = if (tree.left is ChildHole) true else fillAll(tree.left)

                val leftHole = depthOfHole(tree.left)
                val riteHole = depthOfHole(tree.rite)
                if (leftHole == -1 && riteHole == -1) return false
                if (leftHole == 0) TODO("Fill this one")
                else if (riteHole == 0) TODO("Fill this one")
                else if ((leftHole < riteHole || riteHole == -1) && leftHole != -1)
                    return fillAll(tree.left) // Could also just fill one but why not
                else if ((riteHole < leftHole || leftHole == -1) && riteHole != -1)
                    return fillAll(tree.rite)
                else throw Exception("Missed case")
            }
            is LabelNode -> {
                val depths = tree.params.map { depthOfHole(it) }
                val closestHole =
                    depths.fold(-1) { prev, curr -> if (minUnlessNegative(prev, curr) == prev) prev else curr }
                val indToFill = depths.indexOf(closestHole)
                // TODO will throw exception if tree param is a hole i think
                return if (indToFill > -1) fillAll(tree.params[indToFill])  // Why not
                else false
            }
        }
    }

    private fun minUnlessNegative(a: Int, b: Int): Int =
        if (a < 0) b else if (b < 0) a else a.coerceAtMost(b)

    private fun depthOfHole(t: Type): Int {
        fun depthOfHoleHelper(t: Type, acc: Int): Int {
            return when (t) {
                is Error -> -1
                is Function -> minUnlessNegative(depthOfHoleHelper(t.left, acc + 1), depthOfHoleHelper(t.rite, acc + 1))
                is LabelNode -> if (t.label is NameHole) acc
                else acc + 1 + t.typeParams.fold(-1) { a, param -> minUnlessNegative(a, depthOfHoleHelper(param, 0)) }
                is TypeHole -> acc
                is Variable -> -1
            }
        }
        return depthOfHoleHelper(t, 0)
    }

    fun enumerate(): Set<Assignment> {
        var x = 0
        do {
            val tmp = guesses.flatMap { candidateAssignment ->
                val depths = candidateAssignment.entries.associate { (k, v) -> Pair(k, depthOfHole(v)) }
                val (fnName, _) = depths.filterValues { it != -1 }.minBy { it.value }

                fill(candidateAssignment[fnName]!!).map { newType ->
                    (candidateAssignment.minus(fnName) + (mapOf(fnName to newType))).toMutableMap()
                }
            }

            val newGuesses: Set<Assignment> = tmp.toSet()
            println("new guesses: $newGuesses")
            val successfulNewGuesses = newGuesses.filter { assignment ->
                posExamples.map { checkApplication(it, assignment) }.all { it !is Error }
            }
            x++
            guesses.clear()
            guesses.addAll(successfulNewGuesses)
            println("successful concrete guesses: ${guesses.filter { it.all { (_, ty) -> depthOfHole(ty) < 0 } }}")

            // TODO think about how effective negative examples are at avoiding making everything a variable.
            if (x == 5) println("HIT THE SAFEGUARD")
        } while (!(guesses.any { it.all { (_, ty) -> depthOfHole(ty) < 0 } }) && x < 5) // TODO remove this safeguard
        // TODO if there are names still that are not in the set solved, but we are out of guesses, that means everything has a conflict. unsat
        return guesses.filter { it.all { (_, ty) -> depthOfHole(ty) < 0 } }.toSet()
    }

    private fun checkApplication(app: Application, map: Map<String, Type>): Type =
        checkApplicationHelper(app, map, mutableMapOf()).first

    private fun checkApplicationHelper(
        app: Application,
        map: Map<String, Type>,
        context: Context
    ): Pair<Type, Context> {
        var currContext = context
        var fn = map[app.name] ?: throw Exception("Function name not found")
        app.arguments?.forEach {
            val (argType, newContext) = checkApplicationHelper(it, map, currContext)
            currContext = newContext
            val (resultType, resultContext) = u.apply(fn, argType, currContext)
            currContext = resultContext
            fn = resultType
        }
        return Pair(fn, currContext)
    }
}