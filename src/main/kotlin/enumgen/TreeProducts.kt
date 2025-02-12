package enumgen

fun SearchNode.types(root: Boolean): Set<Type> {
    if (root) {
        return this.ports.fold(setOf()) { acc, port ->
            acc.union(port.fold(setOf()) { a, c -> a.union(c.types(root = false)) })
        }
    }
    if (this.ports.isEmpty() || this.ports.any { it.isEmpty() }) {
        return setOf(this.type)  // concrete type or unfinished leaf
    }

    val result = mutableSetOf<Type>()
    val expandedPorts = this.ports.map { port ->
        port.fold(setOf<Type>()) { acc, portOption ->
            acc.union(portOption.types(root = false))
        }.toList()
    }
    naryCartesianProduct(expandedPorts).forEach { selection ->
        result.add(merge(selection))
    }
    return result
}

fun SearchNode.leaves(): Set<Type> {
    if (this.ports.isEmpty()) return setOf(this.type)
    if (this.ports.all { it.isEmpty() }) return setOf(this.type)
    return this.ports.fold(setOf()) { a, p ->
        val tmp = p.flatMap { it.leaves() }.toSet()
        a.union(tmp)
    }
}

fun SearchState.partialContexts(): Set<Map<String, Type>> {
    val possTys = this.names.map { f ->
        if (this.tree(f).ports[0].isEmpty()) throw Exception("Can't find a type!")
        else this.tree(f).leaves().toList()
    }
    return naryCartesianProduct(possTys).map { this.names.zip(it).toMap() }.toSet()
}

fun SearchState.contexts(): Set<Map<String, Type>> {
    val possTys = this.names.map { f ->
        if (this.tree(f).ports[0].isEmpty()) throw Exception("Can't find a type!")
        else this.tree(f).types(root = true).toList()
    }
    return naryCartesianProduct(possTys).map { this.names.zip(it).toMap() }.toSet()
}

/*
[[a, b]] should become [[a], [b]]
[[a, b], [c, d]] > [[a, c], [a, d], [b, c], [b, d]]
 */

fun main() {
    val l1 = listOf(Variable("a"), Variable("b"))
    val l2 = listOf(Variable("c"), Variable("d"))
    println(naryCartesianProduct(listOf(l1)))
    println(naryCartesianProduct(listOf(l1, l2)))
}

fun naryCartesianProduct(tys: List<List<Type>>): Set<List<Type>> {
    if (tys.isEmpty()) return setOf()
    var result = tys[0].map { listOf(it) }.toSet()
    var rest = tys.drop(1)
    while (rest.isNotEmpty()) {
        result = binaryCartesianProduct(result, rest[0])
        rest = rest.drop(1)
    }
    return result
}

fun binaryCartesianProduct(a: Set<List<Type>>, b: List<Type>): Set<List<Type>> {
    val result = mutableSetOf<List<Type>>()
    a.forEach { ita -> b.forEach { itb -> result.add(ita + itb) } }
    return result
}

object MergeException : Exception("Merged mismatched types")

fun merge(tys: List<Type>): Type {
    assert(tys.isNotEmpty())

    val (siblingHoles, noSiblings) = tys.partition { it is SiblingHole }
    return if (siblingHoles.size <= 1 && noSiblings.isNotEmpty()) {
        checkEqMerge(noSiblings)
    } else if (noSiblings.isEmpty()) {
        checkEqMerge(siblingHoles)
    } else throw MergeException
}

private fun checkEqMerge(tys: List<Type>): Type {
    when (tys[0]) {
        is Variable -> {
            if (tys.all { it is Variable } && tys.all { (it as Variable).id == (tys[0] as Variable).id }) return tys[0]
            else throw MergeException
        }
        is Function -> {
            if (tys.all { it is Function })
                return Function(
                    left = merge(tys.map { (it as Function).left }),
                    rite = merge(tys.map { (it as Function).rite })
                )
            else throw MergeException
        }
        is LabelNode -> {
            if (tys.all {
                    it is LabelNode
                            && it.label == (tys[0] as LabelNode).label
                            && it.params.size == (tys[0] as LabelNode).params.size
                })
                return LabelNode(
                    label = (tys[0] as LabelNode).label,
                    params = zip(*tys.map { (it as LabelNode).params }.toTypedArray()).map { param -> merge(param) })
            else throw MergeException
        }
        is ChildHole -> {
            if (tys.all { it is ChildHole }) return tys[0]
            else throw MergeException
        }
        is SiblingHole -> {
            if (tys.all { it is SiblingHole } && tys.all { (it as SiblingHole).depth == (tys[0] as SiblingHole).depth }) return tys[0]
            else throw MergeException
        }
        is Error -> throw MergeException
    }
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