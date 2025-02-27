package enumgen

import enumgen.types.*
import enumgen.types.Function

class SearchState(
    val names: List<String>,
    private val trees: Map<String, SearchNode> = names.associateWith { SearchNode(ChildHole()) }
    // todo better encapsulation would be if nobody can set trees... how to do this
) {
    constructor(skeletons: Map<String, Type>) : this(
        skeletons.keys.toList(),
        skeletons.mapValues { (_, t) -> nodeFor(t) })

    val allTrees = names.map { trees[it]!! }
    fun tree(fn: String) = if (fn in trees) trees[fn]!! else throw Exception("Surprising")

    companion object {
        fun nodeFor(t: Type): SearchNode = SearchNode(t)
//            when (t) {
//            is Error, is TypeHole, is Variable, is LabelNode -> SearchNode(t)
//            is Function -> {
//                if (t.left is ChildHole && t.rite is ChildHole) SearchNode(t)
//                else if (t.left is ChildHole) SearchNode(t, (0 until t.recursiveNumChildHoles()).map{})
//            }
//        }

    }
}

typealias PortContents = MutableList<SearchNode>

class SearchNode(
    val type: Type,
    val ports: ArrayList<PortContents> = ArrayList(List(type.recursiveNumChildHoles()) { mutableListOf() })
) {
    /** gotta be function bc weird init order thing TODO maybe this is ok */
    val numPorts by lazy { ports.size } //= children.size
}
