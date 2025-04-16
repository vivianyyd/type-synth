package util

data class ParameterNode(val f: String, val i: Int) {
    private var ctr = 0
    fun freshArgument() = ArgumentNode(f, i, ctr++)
    override fun toString(): String = "$f-$i"
}

data class ArgumentNode(val f: String, val i: Int, val id: Int)

sealed interface Edge

/** directed, variables subset relation */
data class DependencyEdge(val sub: ParameterNode, val sup: ParameterNode) : Edge {
    override fun toString(): String = "$sub -> $sup"
}
// TODO is it weird that this is a data class but [LinkEdge] isn't?

/** undirected, otherwise nonempty intersection */
class LinkEdge(val a: ParameterNode, val b: ParameterNode) : Edge {
    override fun equals(other: Any?): Boolean {
        if (other !is LinkEdge) return false
        return (a == other.a && b == other.b) || (a == other.b && b == other.a)
    }

    override fun hashCode(): Int {
        return a.hashCode() + b.hashCode()  // TODO aaa
    }
}

/** TODO maybe these should just be a type of dependency */
class SelfLoop(val a: ParameterNode) : Edge

// TODO decide if nodes/edges should be constructed in init block or by DepAnalysis class and only stored here
class DependencyGraph(
    val name: String,
    val nodes: Set<ParameterNode>,
    val deps: Set<DependencyEdge>,
    val loops: Set<SelfLoop>
) {
    /**
     * Invariants: all [f] fields of contained nodes are the same. All edges only contain those nodes
     */
    val edges: Set<Edge> by lazy { deps + loops }
}