package enumgen

class SearchTree(private val names: List<String>) {
    val root = LangNode(names)
}

abstract class SearchNode {
    /** List of ports. Elements are null if port hasn't been filled yet. Empty list if port cannot be satisfied */
    abstract val children: ArrayList<MutableList<SearchNode>?>  // TODO not good encapsulation
    val numPorts = children.size
    fun optionsForHole(port: Int): List<SearchNode>? = children[port]

    fun addChildren(newChildren: List<MutableList<SearchNode>>) {
        assert(children.all {it == null})
        assert(newChildren.size == numPorts)
        newChildren.forEachIndexed{ i, c -> children[i] = c }
    }
}

class LangNode(val names: List<String>) : SearchNode() {
    val functions: ArrayList<MutableList<SearchNode>?> = ArrayList(names.map { null })

    override val children = functions
}

class TypeSearchNode(val type: Type) : SearchNode() {
    // val parent: SearchNode
    override val children: ArrayList<MutableList<SearchNode>?> = ArrayList(List(type.recursiveNumChildHoles()) { null })
}
