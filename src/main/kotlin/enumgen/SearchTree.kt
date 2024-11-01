package enumgen

class SearchTree(private val names: List<String>) {
    val root = LangNode(names)
}

sealed class SearchNode {
    /** List of ports. Elements are null if port hasn't been filled yet. Empty list if port cannot be satisfied */
    abstract val children: ArrayList<MutableList<TypeSearchNode>?>  // TODO not good encapsulation
    val numPorts = children.size
    fun optionsForHole(port: Int): List<TypeSearchNode>? = children[port]

    fun addChildren(newChildren: List<MutableList<TypeSearchNode>>) {
        assert(children.all {it == null})
        assert(newChildren.size == numPorts)
        newChildren.forEachIndexed{ i, c -> children[i] = c }
    }
}

class LangNode(val names: List<String>) : SearchNode() {
    val functions: ArrayList<MutableList<TypeSearchNode>?> = ArrayList(names.map { null })

    override val children = functions
}

class TypeSearchNode(val type: Type) : SearchNode() {
    // val parent: SearchNode
    override val children: ArrayList<MutableList<TypeSearchNode>?> = ArrayList(List(type.recursiveNumChildHoles()) { null })
}
