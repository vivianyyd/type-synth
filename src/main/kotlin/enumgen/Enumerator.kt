package enumgen

import io.michaelrocks.bimap.HashBiMap

class Example {
    // TODO
}

typealias Name = String

typealias Expansion = Pair<Name, Type>

/**
 * f -> (proposed type of f -> {conflicting function expansions})
 * Later: Invariant that it's bidirectional
 *
 * Choose to do this nested Map instead of a BiMap between expansions because if we fully concretize a type, we can erase
 * data to save space
 * */
//typealias ConflictMap = HashMap<Name, HashMap<Type, Set<Expansion>>>
typealias Guesses = MutableMap<String, ArrayDeque<Type>>

private fun Guesses.more() =
    this.entries.fold(false) { acc, (_, guesses) -> !guesses.isEmpty() || acc }

class Enumerator(val names: List<Name>, val examples: Set<Example>) {
    // Enumerate in same order as Unify traverses? Will it reduce to DFS?
    // Invariant: All types here may unify with something. How to keep pairwise conflicts?
    // Heuristic: lower priority in heap if more conflicts
    val guesses = names.associateWith { ArrayDeque(listOf(Incomplete as Type)) }.toMutableMap()
    val conflicts = HashBiMap<Expansion, Expansion>()
    val solved = setOf<Name>()

    var counter = 0
    /** Returns the index of the next function to step */
    private fun next(): Int {
        counter = (counter + 1) % names.size
        return if (names[counter] in solved) next() else counter
    }

    private fun enumerate() {
        while (guesses.more()) {
            TODO(0)
            // TODO fill one hole, then try any complete trees? or randomly try with stuff?
        }
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