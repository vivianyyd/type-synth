package enumgen

// TODO add class which helps indent dedent

class Visualizer(private val tree: SearchTree) {
    private var ctr = 0
    private val sb = StringBuilder()

    private fun display(type: Type): String = when (type) {
        is Error -> "Error"
        is Function -> "(${type.left}) -\\> ${if (type.rite is Function) display(type.rite) else "(${display(type.rite)})"}"
        is LabelNode -> "${type.label}\\<${type.params.joinToString { display(it) }}\\>"
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
        val childTags = this.children.map { "l${ctr++}" }
        sb.append("$gNode[label = \"{ ${display(this.type)} | {${childTags.joinToString(separator = " | "){"<$it>"} }}}\"];\n")
        val children = this.children.map { it?.map {n -> n.viz()}}
        arrows(childTags.map { "\"$gNode\":$it" }, children)
        return gNode
    }

    /** Draws arrows from ports to appropriate children */
    private fun arrows(ports: List<String>, children: List<List<String>?>) {
        ports.forEachIndexed { iPort, port ->
            children[iPort]?.run { this.forEach { sb.append("$port:s -> $it:n;\n") } }
        }
    }

    fun viz(): String {
        sb.append("digraph g {\n")
        sb.append("splines=false;\n")
        sb.append("node [shape = record,height=.1];\n")
        val tags = tree.root.names.associateWith { "fn${ctr++}" }
        sb.append("root[label = \"${tree.root.names.joinToString(separator = " | ") { "<${tags[it]}> $it" }}\"];\n")
        val fns = tree.root.functions.map { it?.map { n -> n.viz() } }
        arrows(tree.root.names.map { "\"root\":${tags[it]}" }, fns)

        sb.append("}")
        return sb.toString()
//        "node0":f2:s -> "node4";
        // node0[label = "{<f1> &beta; | { <f0> |<f2> }}"];
    }


}
