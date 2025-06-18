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

data class SelfLoop(val node: ParameterNode) : Edge

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