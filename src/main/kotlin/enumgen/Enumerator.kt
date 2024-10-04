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

object FilledCompleteTree : Exception()

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

    private fun containsHole(tree: Type): Boolean {
        return TODO()
    }

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
            // TODO This doesn't go deep enough. Needs to be recursive call, otherwise holes two layers down will
            //  never get filled
            //  before recursive call, we check if subtrees contain holes then call if there is. then return trees
            //  constructed from result by mapping.
            //  maybe in complete case we return empty list. Then after each recursive call assert the list isn't empty
            //  since we should never call if the tree is complete
            is Variable -> return if (tree.id is NameHole) nameExpansion.map { Variable(it) } else throw FilledCompleteTree
            is Function -> return if (tree.param is TypeHole) typeExpansion.map { tree.copy(param = it) }
            else if (tree.out is TypeHole) typeExpansion.map { tree.copy(out = it) }
            else
            /* TODO for example this is not sufficient to determine that this node contains no holes in its subtree.
                we need to just check each child for completeness and if contains a hole, blindly call fill on that
                child. then we also don't need to call typeExpansion all those other times, we just call fill on them.
                still need to map on the result to nest it within this node's structure tho. */ throw FilledCompleteTree
            is Node -> return if (tree.label is NameHole) nameExpansion.map { tree.copy(label = it) } else {
                val holeLoc = tree.typeParams.indexOfFirst { it is TypeHole }
                if (holeLoc != -1)
                    typeExpansion.map { newTy ->
                        tree.copy(typeParams = tree.typeParams.mapIndexed { ind, ogTy ->
                            if (ind == holeLoc) newTy else ogTy
                        })
                    }
                else throw FilledCompleteTree
            }
            Error -> throw FilledCompleteTree
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