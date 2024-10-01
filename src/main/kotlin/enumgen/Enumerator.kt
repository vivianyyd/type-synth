package enumgen

import io.michaelrocks.bimap.HashBiMap

class Example {
    // TODO
}

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

class Enumerator(val names: List<String>, val examples: Set<Example>) {
    // Enumerate in same order as Unify traverses? Will it reduce to DFS?
    // Invariant: All types here may unify with something. How to keep pairwise conflicts?
    // Heuristic: lower priority in heap if more conflicts
    // TODO invariant: If a function is completely solved, it is not in guesses
    private val guesses: Guesses = names.associateWith { listOf(TypeHole() as Type) }.toMutableMap()
    private val conflicts = HashBiMap<Expansion, Expansion>()
    private val solved = mutableMapOf<String, Type>()

    var counter = 0

    /** Returns the index of the next function to step */
    private fun next(): Int {
        counter = (counter + 1) % names.size
        return if (names[counter] in solved) next() else counter
    }

    /** Returns a list of trees resulting from replacing one hole in [tree] with all productions */
    private fun fill(tree: Type): List<Type> {
        val typeExpansion = listOf(
            Variable(NameHole()),
            Function(TypeHole(), TypeHole()),
            Node(NameHole(), listOf(TypeHole()))
        )

        // TODO consider how to find variable names and node labels. Pick from fixed set?
        //  Can we do something cleverer based on output of unify?
        val nameExpansion = listOf<Name>()

        fun indexOfTypeHole(l: List<Type>): Int {
            for (i in l.indices) {
                if (l[i] is TypeHole) return i
            }
            return -1
        }

        when (tree) {
            is TypeHole -> return typeExpansion
            // TODO just put this check into a separate thing that checks if complete tree already.
            //  No need to loop through trees with no holes, even though we need to keep them around as guesses since
            //  we don't know if the types of other fns they're compatible with work yet
            // no-op if it's already filled.
            is Variable -> return if (tree.id is NameHole) nameExpansion.map { Variable(it) } else listOf(tree)
            is Function -> return if (tree.param is TypeHole) typeExpansion.map { tree.copy(param = it) }
            else if (tree.out is TypeHole) typeExpansion.map { tree.copy(out = it) } else listOf(tree)
            is Node -> return if (tree.label is NameHole) nameExpansion.map { tree.copy(label = it) } else {
                val holeLoc = indexOfTypeHole(tree.typeParams)
                if (holeLoc != -1)
                    typeExpansion.map { ty ->
                        tree.copy(typeParams=tree.typeParams.indices.map {
                            if (it != holeLoc) tree.typeParams[it] else ty
                        })
                    }
                else listOf(tree)
            }
            Error -> throw Exception("Why")
        }

        // TODO we will need to modify unify to unify nodes with type holes
        //   idea. if l of inc, inc, that unifies with l of a, b, c.
        //   but l of a, inc doesn't.
        //   nor does l of inc, inc, inc, inc, since it definitely has too many
        //   otherwise, we will have trouble figuring out how many params there are thru enumeration.

        //  for nodes, begin by figuring out how many args by filling a bunch of incompletes. then start filling in holes after we figure out the number. ex. l of inc gets filled to l of inc, inc
        //  alternative: fill one arg at a time, always ending the list with an Incomplete. and unify says it is ok as long as the first params match, and incomplete expands to one or more additional params. ex. l of inc gets filled to l of var, inc; l of fn, inc; l of node, inc.
        //    but then if we will leftmost first, we can get a really deep left side
    }

    private fun enumerate() {
        while (guesses.more()) {
            for (name in guesses.keys) {
                guesses[name] = guesses.remove(name)?.flatMap { fill(it) } ?: throw Exception("This shouldn't happen")
            }
            // TODO for all combinations of guesses (+solve values if some are solved),
            //  test the examples of successful applications and record conflicts



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