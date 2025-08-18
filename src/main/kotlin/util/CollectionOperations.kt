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
//    val s = listOf(0, 1, 2, 3)
//    val repetitions = 3
//    val seq = reflexiveNaryProduct(s, repetitions)
//    println("Total: ${seq.toList().size}")
//    println("Total: ${seq.toSet().size}")
//    val slowGroundTruth = naryCartesianProduct((1..repetitions).map { s }).toSet()
//    assert(seq.toSet() == slowGroundTruth)
//    println(seq.toSet().size)
//    println(seq.toList().map { it.reversed() })

    /*
    [1, 3, 5]
    [1, 4, 5]
    [2, 3, 5]
    [2, 4, 5]
     */
    val sets = listOf(listOf(1, 2), listOf(3, 4), listOf(5))
    val product = lazyCartesianProduct(sets)
    for (item in product) {
        println(item)
    }

}

fun <T> reflexiveNaryProduct(set: List<T>, n: Int): Sequence<List<T>> = sequence {
    val indices = Array(n) { 0 }
    val set = set.toSet().toList()
    yield(indices.map { set[it] })
    for (base in 2..set.size) {
        for (i in 0 until n) indices[i] = 0
        while (indices.any { it < base - 1 }) {
            assert(indices.all { it < base })
            // TODO ACTUALLY CLEAN THIS UP THERE'S DUPLICATED CODE WHY
            if (!indices.contains(base - 1)) {
                assert(indices[0] == 0)
                indices[0] = base - 1
            } else {
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
            }
            yield(indices.map { set[it] })
        }
    }
}


fun <T> lazyCartesianProduct(sets: List<List<T>>): Sequence<List<T>> =
    lazySeqCartesianProduct(sets.map { it.asSequence() })

fun <T> lazySeqCartesianProduct(sets: List<Sequence<T>>): Sequence<List<T>> {
    if (sets.isEmpty()) return emptySequence()
    return sets.fold(sequenceOf(emptyList())) { acc, set ->
        acc.flatMap { partial ->
            set.map { element -> partial + element }
        }
    }
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

fun <T> binaryCartesianProduct(a: Set<List<T>>, b: Collection<T>): Set<List<T>> {
    val result = mutableSetOf<List<T>>()
    a.forEach { ita -> b.forEach { itb -> result.add(ita + itb) } }
    return result
//    return a.flatMap { ita -> b.asSequence().map { itb -> ita + itb } }
}

/**
 * Returns a list of lists, each built from elements of all lists with the same indexes.
 * Output has length of shortest input list.
 */
fun <T> zip(vararg lists: List<T>): List<List<T>> {
    return zip(*lists, transform = { it })
}

/**
 * Returns a list of values built from elements of all lists with same indexes using provided [transform].
 * Output has length of shortest input list.
 */
inline fun <T, V> zip(vararg lists: List<T>, transform: (List<T>) -> V): List<V> {
    val minSize = lists.minOfOrNull(List<T>::size) ?: return emptyList()
    val list = ArrayList<V>(minSize)
    val iterators = lists.map { it.iterator() }
    var i = 0
    while (i < minSize) {
        list.add(transform(iterators.map { it.next() }))
        i++
    }

    return list
}