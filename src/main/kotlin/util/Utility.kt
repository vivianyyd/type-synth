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

fun main() {
    val seq = reflexiveNaryProduct(listOf(0, 1, 2, 3), 3)
        seq.forEach{println(it)}
    println("Total: ${seq.toSet().size}")
}

fun <T> reflexiveNaryProduct(set: List<T>, n: Int): Sequence<List<T>> = sequence {
    val indices = Array(n) { 0 }
    var toInc = 0
    yield(indices.map { set[it] })
    while (indices.any { it < set.size - 1 }) {
        assert(indices.all { it < set.size })
        if (indices[toInc] < set.size - 1) indices[toInc] = indices[toInc] + 1
        else {  // carry
            var ptr = toInc
            while (ptr < indices.size && indices[ptr] == set.size - 1) {
                indices[ptr] = 0
                ptr++
            }
            if (ptr >= indices.size) throw Exception("This shouldn't happen")
            else indices[ptr] = indices[ptr] + 1
            toInc = 0
        }
        yield(indices.map { set[it] })
    }
//    return naryCartesianProduct((1..n).map { set })
}

fun <T> naryCartesianProduct(sets: List<List<T>>): Set<List<T>> {
    // TODO Make me lazy
    if (sets.isEmpty()) return setOf()
    var result = sets[0].map { listOf(it) }.toSet()
    var rest = sets.drop(1)
    while (rest.isNotEmpty()) {
        result = binaryCartesianProduct(result, rest[0])
        rest = rest.drop(1)
    }
    return result
}

fun <T> binaryCartesianProduct(a: Set<List<T>>, b: Collection<T>): Set<List<T>> {
    val result = mutableSetOf<List<T>>()
    a.forEach { ita -> b.forEach { itb -> result.add(ita + itb) } }
    return result
//    return a.flatMap { ita -> b.asSequence().map { itb -> ita + itb } }
}
