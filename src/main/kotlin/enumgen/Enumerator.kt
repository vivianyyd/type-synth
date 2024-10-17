package enumgen

/**
 * If [arguments] is null, the function [name] is not applied.
 *
 * Later: If [arguments] is empty, [name] is applied with no arguments. For now, unit doesn't exist, all fn must have an
 * argument to be applied, this is WLOG since we can just have a unit value be passed
 */
data class Application(val name: String, val arguments: List<Application>?)

typealias Expansion = Pair<String, Type>

/**
 * f -> (proposed type of f -> {conflicting function expansions})
 * Later: Invariant that it's bidirectional
 *
 * Choose to do this nested Map instead of a BiMap between expansions because if we fully concretize a type, we can erase
 * all exps for that name to save space
 * */
//typealias ConflictMap = HashMap<String, HashMap<Type, Set<Expansion>>>

typealias Assignment = MutableMap<String, Type>

class Enumerator(
    private val names: List<String>,
    private val posExamples: Set<Application>,
    private val MAX_TYPE_PARAMS: Int
) {
    private val u = Unify()  // TODO make this less dumb
    private val guesses: MutableSet<Assignment> = mutableSetOf(names.associateWith { TypeHole() }.toMutableMap())

    init {
//        TODO("Assert that [posExamples] only contains names in [names]")
    }

    // TODO invariant: If a function is completely solved, it is not in guesses
    private var counter = 0

    // TODO what if we keep around a lot of duplicate trees because of renaming and alpha equivalence
    private val nameExpansion = listOf(NameLiteral("0"), NameLiteral("1"), NameLiteral("2"))

    private val typeExpansion =
        listOf(Function(TypeHole(), TypeHole())) +
                nameExpansion.map { Variable(it) } +
                (0..MAX_TYPE_PARAMS).map { Node(NameHole(), List(it) { TypeHole() }) }

    /**
     * Returns a list of trees resulting from replacing one hole in [tree] with all productions
     *
     * If there are no holes in [tree], returns empty list.
     */
    private fun fill(tree: Type): List<Type> {
        when (tree) {
            is TypeHole -> return typeExpansion
            is Variable -> return listOf()
            is Function -> {
                val paramHole = depthOfHole(tree.param)
                val outHole = depthOfHole(tree.out)
                if (paramHole == -1 && outHole == -1) return listOf()
                return if ((paramHole < outHole || outHole == -1) && paramHole != -1)
                    fill(tree.param).map { tree.copy(param = it) }
                else fill(tree.out).map { tree.copy(out = it) }
            }
            is Node -> {
                if (tree.label is NameHole) return nameExpansion.map { tree.copy(label = it) }

                val depths = tree.typeParams.map { depthOfHole(it) }
                val closestHole =
                    depths.fold(-1) { prev, curr -> if (minUnlessNegative(prev, curr) == prev) prev else curr }
                val indToFill = depths.indexOf(closestHole)
                if (indToFill > -1) {
                    val iParamTrees = fill(tree.typeParams[indToFill])
                    if (iParamTrees.isNotEmpty()) {
                        return iParamTrees.map { newTy ->
                            tree.copy(typeParams = tree.typeParams.mapIndexed { ind, ogTy -> if (ind == indToFill) newTy else ogTy })
                        }
                    }
                }
                return listOf()
            }
            is Error -> return listOf()
        }
    }

    private fun cartesianProduct(candidates: Map<String, List<Type>>): List<Map<String, Type>> {
        // Need to init or else flatMap won't work
        var result: List<Map<String, Type>> = candidates[names[0]]?.map {
            mapOf(names[0] to it)
        } ?: throw Exception("there are no functions")

        candidates.forEach { (name, types) ->
            if (name != names[0]) {
                result = result.flatMap { mapping ->
                    // For each partial context, make |[types]| new maps which are the context plus a candidate for [name].
                    types.map { ty -> mapping + mapOf(name to ty) }
                }
            }
        }
        return result
    }

    private fun minUnlessNegative(a: Int, b: Int): Int =
        if (a < 0) b else if (b < 0) a else a.coerceAtMost(b)

    private fun depthOfHole(t: Type): Int {
        fun depthOfHoleHelper(t: Type, acc: Int): Int {
            return when (t) {
                is Error -> -1
                is Function -> minUnlessNegative(depthOfHoleHelper(t.param, acc + 1), depthOfHoleHelper(t.out, acc + 1))
                is Node -> if (t.label is NameHole) acc
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

            // TODO possible speedup is instead of adding solved to typesToTry, separately look them up when typechecking
            //  examples. there shouldn't actually be much speedup bc solved types add no branching. but maybe less memory idk

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