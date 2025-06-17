package oldenumgen

import types.*
import types.Function
import util.naryCartesianProduct
import util.zip

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
        result.add(merge(selection))  // TODO Make me lazy
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
    return naryCartesianProduct(possTys).map { this.names.zip(it).toMap() }.toSet()  // TODO Make me lazy
}

fun SearchState.contexts(): Set<Map<String, Type>> {
    val possTys = this.names.map { f ->
        if (this.tree(f).ports[0].isEmpty()) throw Exception("Can't find a type!")
        else this.tree(f).types(root = true).toList()
    }
    return naryCartesianProduct(possTys).map { this.names.zip(it).toMap() }.toSet()  // TODO Make me lazy
}

object MergeException : Exception("Merged mismatched types")

fun merge(tys: List<Type>): Type {
    assert(tys.isNotEmpty())

    val (siblingHoles, noSiblings) = tys.partition { it is SiblingHole }
    return if (noSiblings.isNotEmpty()) {
        if (siblingHoles.isNotEmpty()) checkEqMerge(siblingHoles)  // Make sure sibling holes are same depth, throw away result
        checkEqMerge(noSiblings)
    } else {
        checkEqMerge(siblingHoles)
    }
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
