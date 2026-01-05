package util

import query.FlatApp

interface PrefixContainment {
    fun addAll(exs: List<FlatApp>)

    /**
     * Check whether this example is a prefix of any element added to the data structure, modulo
     * equivalence.
     */
    fun lookup(ex: FlatApp): Boolean
}

/** This should be implemented as a prefix tree, but for now, it is brute force */
class PrefixBruteForce(private val oracle: Oracle) : PrefixContainment {
    private val seen = mutableListOf<FlatApp>()

    override fun addAll(exs: List<FlatApp>) {
        seen.addAll(exs)
    }

    override fun lookup(ex: FlatApp): Boolean {
        return seen
            .filter { it.name == ex.name && it.args.size >= ex.args.size }
            .any { oracle.flatEqual(FlatApp(it.name, it.args.subList(0, ex.args.size)), ex) }
    }
}

/*
TODO: Make a prefix tree for all posexs where nodes represent obs equivalence (so it may be a dag)
for instance, examples for f: 'a -> 'b -> Int have the shape
         f
       /   \
f (x|x')     f(y)
       \   /
 f(x|x'|y, z|w|m|n)
where x, x' are obs equiv
*/
