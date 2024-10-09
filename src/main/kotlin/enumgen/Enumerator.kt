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

    /* TODO
        What if instead of tracking constraints as the disjunction of negations of trees, we represent our choices
        as a single subtree/selection of the tree where the root is a tuple of types, one element for each function
        Then when we eliminate a choice, we eliminate a complete subtree
        we only ever try combinations anyway. why not enumerate them that way


        SMT way: build in constraints. if we ever want to make a new candidate combo, check whether violates constraints
        but if we just top down enum using a queue, we just remove anything that will violate constraints bc we go top down
        we can match against stuff. like if the fn param type doesn't work, we can delete anything with the same param type
        regardless of the out type. but maybe we can essentially do the same thing by only perform one enum step one group at a time
     */


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
            println("guesses at start of loop $guesses")
            val tmp = guesses.flatMap { candidateAssignment ->

                // In each assignment, fill one fn's type's hole
                var tmpMinDepth = -1

                val depths = candidateAssignment.entries.associate { (k, v) -> Pair(k, depthOfHole(v)) }
                val (fnName, _) = depths.filterValues { it != -1 }.minBy { it.value }

                println("FILLING FOR $fnName")
                val filled = fill(candidateAssignment[fnName]!!)
                val tmptmp = filled.map { newType ->
                    (candidateAssignment.minus(fnName) + (mapOf(fnName to newType))).toMutableMap()
                }
                tmptmp
            }

            val newGuesses: Set<Assignment> = tmp.toSet()

            println("new guesses: $newGuesses")
            println("new concrete guesses: ${newGuesses.filter { it.all { (_, ty) -> depthOfHole(ty) < 0 } }}")
            val successfulNewGuesses = newGuesses.filter { assignment ->
                posExamples.map { checkApplication(it, assignment) }.all { it !is Error }
            }

            x++
            guesses.clear()
            guesses.addAll(successfulNewGuesses)

            println("successful guesses: $guesses")
            println("successful concrete guesses: ${guesses.filter { it.all { (_, ty) -> depthOfHole(ty) < 0 } }}")

            /* Learning from errors

        Now I think learning from errors is just deleting all the trees with errors

            Unifying a node with a function
                Add a constraint if neither is solved.
                If one is solved, delete the other mismatching one.

            Label mismatch
                Add a constraint if neither is solved.
                If one is solved, delete the other mismatching one.

            Param quantity mismatch
                Add a constraint if neither is solved.
                If one is solved, delete the other mismatching one.

            Applied a non-function A B
                A should be a function. Remove any trees where it is not
                    It's not that simple. What if A is alpha, which gets bound earlier?
                    Can we apply anonymous stuff?
                    C(D, A) where C is alpha -> alpha -> int
                    Then later A(B), lets say A should be beta -> gamma
                    Then these two examples only work if D is a function of any type
                    I think it's ok, because we can just remove examples where A not a function
                    Then we can try all the remaining examples again to see that D not a function should be removed
                    too, or else D won't match with A as alpha. Or we might only have examples where D = A to begin
                    with.
             */

            /*
            Can't just delete tree if error. Need to record combination that's bad

            if we record candidates for each fn separately then the combos are implicit
                we will do cartesian product each time and keep track of bad combos with sat
            if we record all possible combos as different ways of highlighting a gigatree with root
            branching to all fns, allowed combos are explicit and bad combos are implicit, we just delete them

            It really just depends on if we think there are more good combinations or bad ones. Which would we
            rather store directly?
            If we store bad combinations in sat solver, we still have to store types which generate the space of
            possible combinations

            I really don't want to think about smt solvers
             */

            // TODO possible speedup is instead of adding solved to typesToTry, separately look them up when typechecking
            //  examples. there shouldn't actually be much speedup bc solved types add no branching. but maybe less memory idk


            // TODO remember the don't cares. if the param type of a fn is wrong, we don't care the out type

            // TODO think about how effective negative examples are at avoiding making everything a variable.
            if (x == 10) println("HIT THE SAFEGUARD")
        } while (!(guesses.any { it.all { (_, ty) -> depthOfHole(ty) < 0 } }) && x < 5) // TODO remove this safeguard
        // TODO if there are names still that are not in the set solved, but we are out of guesses, that means everything has a conflict. unsat
        return guesses.filter { it.all { (_, ty) -> depthOfHole(ty) < 0 } }.toSet()
    }
/*
A conflict exists in a set of assignments
But the first conflict only occurs between two nodes/functions, one edge

Well the way we'll use it is if we discover something is definitely of the form A,
all trees which conflict with A will be removed from the heaps of their fns

map A -> set of conflicts
for each conflict they should also map to A
 */

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