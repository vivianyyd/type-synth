package enumgen

import io.michaelrocks.bimap.HashBiMap

/**
 * If [arguments] is null, the function [name] is not applied.
 * If [arguments] is empty, [name] is applied with no arguments.
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
typealias Guesses = MutableMap<String, List<Type>>

private fun Guesses.more() =
    this.entries.fold(false) { acc, (_, guesses) -> !guesses.isEmpty() || acc }

class Enumerator(val names: List<String>, val posExamples: Set<Application>, val MAX_TYPE_PARAMS: Int) {
    init {
        TODO("Assert that [posExamples] only contains names in [names]")
    }

    // Enumerate in same order as Unify traverses? Will it reduce to DFS?
    // Invariant: All types here may unify with something. How to keep pairwise conflicts?
    // Heuristic: lower priority in heap if more conflicts
    // TODO invariant: If a function is completely solved, it is not in guesses
    private val guesses: Guesses = names.associateWith { listOf(TypeHole() as Type) }.toMutableMap()
    private val conflicts = HashBiMap<Expansion, Expansion>()
    private val solved = mutableMapOf<String, Type>()

    private var counter = 0

    /** Returns the index of the next function to step */
    private fun next(): Int {
        counter = (counter + 1) % names.size
        return if (names[counter] in solved) next() else counter
    }

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

    private val typeExpansion = listOf(
        Variable(NameHole()),
        Function(TypeHole(), TypeHole()),
    ) + (0..MAX_TYPE_PARAMS).map { Node(NameHole(), List(it) { TypeHole() }) }

    // TODO what if we keep around a lot of duplicate trees because of renaming and alpha equivalence
    private val nameExpansion = listOf<Name>(NameLiteral("0"), NameLiteral("1"), NameLiteral("2"))

    /**
     * Returns a list of trees resulting from replacing one hole in [tree] with all productions
     *
     * If there are no holes in [tree], returns empty list.
     */
    private fun fill(tree: Type): List<Type> {
        when (tree) {
            is TypeHole -> return typeExpansion
            is Variable -> return if (tree.id is NameHole) nameExpansion.map { Variable(it) } else listOf()
            is Function -> {
                val paramTrees = fill(tree.param)
                if (paramTrees.isNotEmpty()) return paramTrees.map { tree.copy(param = it) }
                val outTrees = fill(tree.out)
                if (outTrees.isNotEmpty()) return outTrees.map { tree.copy(out = it) }
                return listOf()
            }
            is Node -> {
                if (tree.label is NameHole) return nameExpansion.map { tree.copy(label = it) }
                for (i in tree.typeParams.indices) {
                    val iParamTrees = fill(tree.typeParams[i])
                    if (iParamTrees.isNotEmpty()) {
                        return iParamTrees.map { newTy ->
                            tree.copy(typeParams = tree.typeParams.mapIndexed { ind, ogTy -> if (ind == i) newTy else ogTy })
                        }
                    }
                }
                return listOf()
            }
            Error -> return listOf()
        }
    }

    private fun cartesianProduct(candidates: Map<String, List<Type>>): List<Map<String, Type>> {
        // Need to init or else flatMap won't work
        var result: List<Map<String, Type>> = candidates[names[0]]?.map {
            mapOf(names[0] to it)
        }?: throw Exception("there are no functions")

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

    private fun enumerate() {
        while (guesses.more()) {
            // Step one name
            val name = names[next()]
            guesses[name] = guesses.remove(name)?.flatMap { fill(it) } ?: throw Exception("This shouldn't happen")

            // Step every fn type at once. This might produce conflicts which are duplicate in spirit,
            // so first let's try filling one at a time
//            for (name in guesses.keys) {
//                guesses[name] = guesses.remove(name)?.flatMap { fill(it) } ?: throw Exception("This shouldn't happen")
//            }

            val typesToTry = guesses + solved.mapValues { (_, ty) -> listOf(ty) }
            if (typesToTry.isEmpty()) throw Exception("wat")

            // For now try testing all combinations.
            //   we can do a try after filling one additional level in one group.
            //   or we can fill all groups then try all combos. we can see which faster empirically
            val jillionMappings = cartesianProduct(typesToTry)
            jillionMappings.forEach { mapping ->
                // TODO try to typecheck every example! record conflicts.

                // TODO possible speedup is instead of adding solved to typesToTry, separately look them up when typechecking
                //  examples. there shouldn't actually be much speedup bc solved types add no branching. but maybe less memory idk

            }

            // TODO figure out what info needs to be in unification error. class with information pointing into the tree so we can learn from it
            // TODO remember the don't cares. if the param type of a fn is wrong, we don't care the out type

            // TODO think about how effective negative examples are at avoiding making everything a variable.

        }
        // TODO if there are names still that are not in the set solved, but we are out of guesses, that means everything has a conflict. unsat
        TODO()
    }

    /*
    A conflict exists in a set of assignments
    But the first conflict only occurs between two nodes/functions, one edge

    Well the way we'll use it is if we discover something is definitely of the form A,
    all trees which conflict with A will be removed from the heaps of their fns

    map A -> set of conflicts
    for each conflict they should also map to A
     */
}