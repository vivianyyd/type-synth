package enumgen

class SearchState(val names: List<String>) {
    private val trees: Map<String, SearchNode> = names.associateWith { SearchNode(ChildHole()) }
    val allTrees = names.map { trees[it]!! }
    fun tree(fn: String) = if (fn in trees) trees[fn]!! else throw Exception("Surprising")
}

typealias PortContents = MutableList<SearchNode>

class SearchNode(val type: Type) {
    val children: ArrayList<PortContents> =
        ArrayList(List(type.recursiveNumChildHoles()) { mutableListOf() })

    /** gotta be function bc weird init order thing TODO maybe this is ok */
    val numPorts by lazy { children.size } //= children.size
}
