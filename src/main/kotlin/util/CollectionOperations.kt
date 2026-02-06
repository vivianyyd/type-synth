package util

fun <T> equivalenceClasses(elems: Collection<T>, equals: (T, T) -> Boolean): Set<Set<T>> {
    val result = mutableSetOf<MutableSet<T>>() // Invariant: No element of the set is empty
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

fun <T> Collection<T>.eqClasses(equals: (T, T) -> Boolean) = equivalenceClasses(this, equals)

/** LLM generated */
fun <T> partitions(list: List<T>): Sequence<List<List<T>>> {
    val n = list.size

    // P(n, k) = all partitions of first n elements into k blocks
    fun gen(n: Int, k: Int): Sequence<List<List<T>>> {
        if (n == 0) {
            return if (k == 0) sequenceOf(emptyList()) else emptySequence()
        }
        if (k == 0) return emptySequence()

        val elem = list[n - 1]

        return sequence {
            // Case 1: element starts a new block
            for (p in gen(n - 1, k - 1)) {
                yield(p + listOf(listOf(elem)))
            }

            // Case 2: element joins one of the existing blocks
            for (p in gen(n - 1, k)) {
                for (i in p.indices) {
                    val newBlock = p[i] + elem
                    val newPart = p.toMutableList().also { it[i] = newBlock }.toList()
                    yield(newPart)
                }
            }
        }
    }

    // yield all partitions by increasing k
    return sequence {
        for (k in 1..n) {
            yieldAll(gen(n, k))
        }
    }
}

fun <T> reflexiveNaryProduct(elems: List<T>, n: Int): Sequence<List<T>> = sequence {
    val indices = Array(n) { 0 }
    val set = elems.toSet().toList()
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
                else { // carry
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

fun <T> lazySeqCartesianProduct(choices: List<Sequence<T>>): Sequence<List<T>> {
    if (choices.isEmpty()) return emptySequence()
    return choices.fold(sequenceOf(emptyList())) { acc, choice ->
        acc.flatMap { partial -> choice.map { option -> partial + option } }
    }
}

/**
 * [trace]: The ids of nodes from root to this product.
 *
 * @yields pairs of child choices and the traces associated with them
 */
// fun nodeProduct(
//    ports: List<Sequence<ConcreteNode>>,
//    trace: List<Int>,
//    conflicts: List<List<Int>>
// ): Sequence<Pair<List<ConcreteNode>, List<Int>>> {
//    fun conflict(trace: List<Int>, conflicts: List<List<Int>>) = conflicts.any { it.all { it in
// trace } }
//
//    if (ports.isEmpty() || conflict(trace, conflicts)) return emptySequence()
//    return ports.fold(sequenceOf(emptyList<ConcreteNode>() to trace)) { acc, port ->
//        acc.flatMap { (prevSiblings, tr) ->
//            port.mapNotNull { option ->
//                val tra = (tr + option.ids).toSet().toList()
//                if (conflict(tra, conflicts)) null
//                else (prevSiblings + option) to tra
//            }
//        }
//    }
// }

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
 * Returns a list of lists, each built from elements of all lists with the same indexes. Output has
 * length of shortest input list.
 */
fun <T> zip(vararg lists: List<T>): List<List<T>> {
    return zip(*lists, transform = { it })
}

/**
 * Returns a list of values built from elements of all lists with same indexes using provided
 * [transform]. Output has length of shortest input list.
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

fun <T> Collection<T>.lines() = this.joinToString(separator = "\n")
