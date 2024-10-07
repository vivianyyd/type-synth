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
        as a single subtree/selection of the tree where the root is a tuple of types, one elment for each function
        Then when we eliminate a choice, we eliminate a complete subtree
     */

    /**
     * Returns a list of trees resulting from replacing one hole in [tree] with all productions
     *
     * If there are no holes in [tree], returns empty list.
     */
    private fun fill(tree: Type): List<Type> {
        val typeExpansion = listOf(
            Variable(NameHole()),
            Function(TypeHole(), TypeHole()),
        ) + (0..MAX_TYPE_PARAMS).map { Node(NameHole(), List(it) { TypeHole() }) }

        val nameExpansion = listOf<Name>(NameLiteral("0"), NameLiteral("1"), NameLiteral("2"))

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

    private fun enumerate() {
        while (guesses.more()) {
            for (name in guesses.keys) {
                guesses[name] = guesses.remove(name)?.flatMap { fill(it) } ?: throw Exception("This shouldn't happen")
            }
            // TODO for all combinations of guesses (+solve values if some are solved),
            //  test the examples of successful applications and record conflicts

            // TODO error needs to be a class with information pointing into the tree so we can learn from it

            // TODO for now try testing all combinations. It's 3^n tried per round of filling where n the number of functions since there are 3 productions.
            //    actually that's not true bc the prev round might've had multiple candidates make it?
            //    we need negative examples or else we will just make everything a variable.
            //   we can do a try after filling one additional level in one group. or we can fill all groups then try all combos. we can see which faster empirically
            // TODO fill one hole, then try any complete trees? <- no need for them to be complete. randomly try with stuff?
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