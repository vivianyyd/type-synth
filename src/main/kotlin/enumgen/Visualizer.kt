package enumgen

class Visualizer(private val tree: SearchTree) {
    private var ctr = 0
    private val dw = DotWriter()

    private fun display(type: Type): String = when (type) {
        is Error -> "Error"
        is Function -> "(${display(type.left)}) &rarr; ${
            if (type.rite is Function) display(type.rite) else "(${
                display(
                    type.rite
                )
            })"
        }"
        is LabelNode -> type.label + (if (type.params.isNotEmpty()) "[${type.params.joinToString { display(it) }}]" else "")
        is ChildHole -> "_"
        is SiblingHole -> "-${type.depth}"
        is Variable -> {
             val greeks = listOf(
            "alpha", "beta", "gamma", "delta", "epsilon", "zeta", "eta", "theta", "iota", "kappa",
            "lambda", "mu", "nu", "xi", "omicron", "pi", "rho", "sigma", "tau", "upsilon", "phi", "chi", "psi", "omega"
            )
            if (type.id in greeks.indices) "&${greeks[type.id]};" else "v${type.id}"
        }
    }

    /** Adds the graphviz code that draws the subtree rooted at [this], and
     * returns the name of the graphviz node representing [this]. */
    private fun TypeSearchNode.viz(): String {
        val gNode = "n${ctr++}"
        val childTags = this.children.map { "c${ctr++}" }
        dw.writeTypeNode(gNode, display(this.type), childTags)
        val children = this.children.map { it?.map { n -> n.viz() } }
        drawArrows(childTags.map { "\"$gNode\":$it" }, children)
        return gNode
    }

    /** Draws arrows from ports to appropriate children */
    private fun drawArrows(ports: List<String>, children: List<List<String>?>) {
        ports.forEachIndexed { iPort, port ->
            children[iPort]?.run { this.forEach { dw.writeEdge(port, it) } }
        }
    }

    fun viz(): String {
        dw.startGraph()
        val tags = tree.root.names.associateWith { "fn${ctr++}" }
        tree.root.names.forEach {
            dw.writeNode("${tags[it]}", it.replace("[", "\\[").replace("]", "\\]"))
        }
        val fns = tree.root.functions.map { it?.map { n -> n.viz() } }
        drawArrows(tree.root.names.map { "\"${tags[it]}\"" }, fns)
        dw.finishGraph()
        return dw.output()
    }
}
