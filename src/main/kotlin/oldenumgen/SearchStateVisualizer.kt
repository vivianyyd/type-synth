package oldenumgen

import types.*
import types.Function
import util.visualizations.TreeDotWriter
import java.io.File
import java.io.FileOutputStream
import java.io.PrintWriter

object SearchStateVisualizer {
    private var ctr = 0
    private val dw = TreeDotWriter()

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
                "alpha",
                "beta",
                "gamma",
                "delta",
                "epsilon",
                "zeta",
                "eta",
                "theta",
                "iota",
                "kappa",
                "lambda",
                "mu",
                "nu",
                "xi",
                "omicron",
                "pi",
                "rho",
                "sigma",
                "tau",
                "upsilon",
                "phi",
                "chi",
                "psi",
                "omega"
            )
            type.id
//            if (type.id in greeks.indices) "&${greeks[type.id]};" else "v${type.id}"
        }
    }

    /** Adds the graphviz code that draws the subtree rooted at [this], and
     * returns the name of the graphviz node representing [this]. */
    private fun SearchNode.display(): String {
        val gNode = "n${ctr++}"
        val childTags = this.ports.map { "c${ctr++}" }
        dw.writeTypeNode(gNode, display(type), childTags)
        val children = this.ports.map { it.map { n -> n.display() } }
        drawArrows(childTags.map { "\"$gNode\":$it" }, children)
        return gNode
    }

    /** Draws arrows from ports to appropriate children */
    private fun drawArrows(ports: List<String>, children: List<List<String>?>) {
        ports.forEachIndexed { iPort, port ->
            children[iPort]?.run {
                this.forEach {
                    dw.writeEdge(port, it)
                }
            }
        }
    }

    private fun visualize(node: SearchNode): String {
        dw.startGraph()
        node.display()
        dw.finishGraph()
        val out = dw.output()
        dw.restart()
        return out
    }

    fun viz(node: SearchNode, fileID: String) = writeDotOutput(visualize(node), fileID)
    fun viz(tree: SearchState, fileID: String) = writeDotOutput(visualize(tree), fileID)

    private fun visualize(state: SearchState): String {
        dw.startGraph()
        val tags = state.names.associateWith { "fn${ctr++}" }
        state.names.forEach {
            dw.writeNode("${tags[it]}", it.replace("[", "\\[").replace("]", "\\]"))
        }
        val fns = state.allTrees.map { n -> n.display() }
        drawArrows(state.names.map { "\"${tags[it]}\"" }, fns.map { listOf(it) })
        dw.finishGraph()
        val out = dw.output()
        dw.restart()
        return out
    }

    fun writeDotOutput(contents: String, id: String) {
        val out = PrintWriter(FileOutputStream("results${File.separator}type-$id.dot"))
        out.println(contents)
        out.close()
    }
}
