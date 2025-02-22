package util

fun <T> equivalenceClasses(elems: Collection<T>, equals: (T, T) -> Boolean): Set<Set<T>> {
    val result = mutableSetOf<MutableSet<T>>()  // Invariant: No element of the set is empty
    elems.forEach { elem ->
        var foundOne = false
        for (eqClass in result) {
            if (equals(elem, eqClass.first())) {
                eqClass.add(elem)
                foundOne = true
                break
            }
        }
        if (!foundOne) result.add(mutableSetOf(elem))
    }
    return result
}

fun <T> reflexiveNaryProduct(set: List<T>, n: Int): Set<List<T>> {
    return naryCartesianProduct((1..n).map { set })
}

fun <T> naryCartesianProduct(sets: List<List<T>>): Set<List<T>> {
    if (sets.isEmpty()) return setOf()
    var result = sets[0].map { listOf(it) }.toSet()
    var rest = sets.drop(1)
    while (rest.isNotEmpty()) {
        result = binaryCartesianProduct(result, rest[0])
        rest = rest.drop(1)
    }
    return result
}

/** Output at index i is a set of (i+1)-ary products. */
fun <T> upToNaryCartesianProduct(sets: Collection<T>, n: Int): List<Set<List<T>>> {
    if (sets.isEmpty()) return listOf()
    val products = mutableListOf(sets.map { listOf(it) }.toSet())  // init to unary products
    for (i in 2..n) {
        products.add(binaryCartesianProduct(products.lastOrNull()!!, sets))
    }
    return products
}

fun <T> binaryCartesianProduct(a: Set<List<T>>, b: Collection<T>): Set<List<T>> {
    val result = mutableSetOf<List<T>>()
    a.forEach { ita -> b.forEach { itb -> result.add(ita + itb) } }
    return result
}
