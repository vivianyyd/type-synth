package enumgen

fun SearchNode.types(): Set<Type> {
    if (this.children.any { it.isNullOrEmpty() }) return setOf()

    val result = mutableSetOf<Type>()
    val expandedChildren = this.children.map { port ->
        port!!.fold(setOf<Type>()) { acc, child ->
            acc.union(child.types())
        }
    }
    naryCartesianProduct(expandedChildren).forEach { selection ->
        result.add(merge(selection))
    }
    return result
}

fun SearchTree.contexts(): Set<Context> {
    val possTys = this.root.names.associateWith{ f->
        if (this.getRootFor(f).children[0].isNullOrEmpty()) throw Exception("Can't find a type!")
        else this.getRootFor(f).children[0]!!.flatMap{it.types()}
    }
    TODO("cartesian product")
}

fun naryCartesianProduct(tys: List<Set<Type>>): Set<List<Type>> {
    if (tys.isEmpty()) return setOf()
    var result = setOf(tys[0].toList())
    var rest = tys.drop(1)
    while (rest.isNotEmpty()) {
        result = binaryCartesianProduct(result, rest[0])
        rest = tys.drop(1)
    }
    return result
}

fun binaryCartesianProduct(a: Set<List<Type>>, b: Set<Type>): Set<List<Type>> {
    val result = mutableSetOf<List<Type>>()
    a.forEach { ita -> b.forEach { itb -> result.add(ita + itb) } }
    return result
}

object MergeException : Exception("Merged mismatched types")

fun merge(tys: List<Type>): Type {
    assert(tys.isNotEmpty())

    val (siblingHoles, noSiblings) = tys.partition{it is SiblingHole}
    if (siblingHoles.size <= 1) return checkEqMerge(noSiblings)
    else throw MergeException
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
        is SiblingHole, is Error -> throw MergeException
    }
}

/**
 * Returns a list of lists, each built from elements of all lists with the same indexes.
 * Output has length of shortest input list.
 */
inline fun <T> zip(vararg lists: List<T>): List<List<T>> {
    return zip(*lists, transform = { it })
}

/**
 * Returns a list of values built from elements of all lists with same indexes using provided [transform].
 * Output has length of shortest input list.
 */
inline fun <T, V> zip(vararg lists: List<T>, transform: (List<T>) -> V): List<V> {
    val minSize = lists.map(List<T>::size).min() ?: return emptyList()
    val list = ArrayList<V>(minSize)

    val iterators = lists.map { it.iterator() }
    var i = 0
    while (i < minSize) {
        list.add(transform(iterators.map { it.next() }))
        i++
    }

    return list
}