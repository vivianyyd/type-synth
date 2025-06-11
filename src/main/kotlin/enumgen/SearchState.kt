package enumgen

import types.ChildHole
import types.Function
import types.Type
import types.recursiveNumChildHoles

class SearchState(
    val names: List<String>,
    private val trees: Map<String, SearchNode> = names.associateWith { SearchNode(ChildHole()) }
    // todo better encapsulation would be if nobody can set trees... how to do this
) {
    constructor(skeletons: Map<String, Type>) : this(
        skeletons.keys.toList(),
        skeletons.mapValues { (_, t) ->
            assert(t is Function || t is ChildHole)
            // Artificially create a root node if we initialize to an arrow skeleton
            if (t is Function) SearchNode(ChildHole(), arrayListOf(mutableListOf(SearchNode(t))))
            else SearchNode(t)
        })

    val allTrees = names.map { trees[it]!! }
    fun tree(fn: String) = if (fn in trees) trees[fn]!! else throw Exception("Surprising")
}

typealias PortContents = MutableList<SearchNode>

class SearchNode(
    val type: Type,
    val ports: ArrayList<PortContents> = ArrayList(List(type.recursiveNumChildHoles()) { mutableListOf() })
) {
    /** gotta be function bc weird init order thing TODO maybe this is ok */
    val numPorts by lazy { ports.size } //= children.size
}
