package enumgen

class SearchTree(private val names: List<String>) {
    val root = LangNode(names)
}

interface SearchNode {
    /** Invariant: [children.size == numPorts] */
    fun children(): ArrayList<MutableList<SearchNode>>
    fun numPorts() = children().size
    fun optionsForHole(port: Int): MutableList<SearchNode> = children()[port]
}

class LangNode(val names: List<String>) : SearchNode {
    val functions: ArrayList<MutableList<SearchNode>> = ArrayList(names.map { mutableListOf() })

    override fun children() = functions
}

interface TypeSearchNode : SearchNode {
//    val parent: SearchNode

    val type: Type
}
