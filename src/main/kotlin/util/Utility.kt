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
    val s = listOf(0, 1, 2, 3)
    val repetitions = 3
    val seq = reflexiveNaryProduct(s, repetitions)
    seq.forEach { println(it.reversed()) }
    println("Total: ${seq.toList().size}")
    println("Total: ${seq.toSet().size}")
    val slowGroundTruth = naryCartesianProduct((1..repetitions).map { s }).toSet()
    println(seq.toSet() == slowGroundTruth)
}

fun <T> reflexiveNaryProduct(set: List<T>, n: Int): Sequence<List<T>> = sequence {
    val indices = Array(n) { 0 }
    yield(indices.map { set[it] })
    for (base in 1..set.size) {
        for (i in 0 until n) indices[i] = 0
        while (indices.any { it < base - 1 }) {
            assert(indices.all { it < base })
            if (indices[0] < base - 1) indices[0] = indices[0] + 1
            else {  // carry
                var ptr = 0
                while (indices[ptr] == base - 1) {
                    indices[ptr] = 0
                    ptr++
                }
                indices[ptr] = indices[ptr] + 1
            }
            if (!indices.contains(base - 1)) {
                assert(indices[0] == 0)
                indices[0] = base - 1
            }
            yield(indices.map { set[it] })
        }
    }
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
