package util.visualizations

import java.io.PrintWriter

class FlowDotWriter {
    private val sb = StringBuilder()

    fun restart() = sb.delete(0, sb.length)

    fun startGraph() {
        sb.append("digraph g {")
        sb.appendLine()
        listOf(
            "splines=true;",
            "rankdir=LR; ordering=out;",
            "node [shape = record, height=.1];"
        ).forEach { sb.append("\t$it\n") }
    }

    fun writeNode(nodeName: String, label: String) {
        sb.append("\t$nodeName [label = \"$label\"];\n")
    }

    fun writeEdges(edges: List<Pair<String, String>>, directed: Boolean, subgraphName: String) {
        sb.append("\tsubgraph $subgraphName {")
        sb.appendLine()
        if (!directed) sb.append("\t\tedge [dir=none, color=purple]\n")
        writeSubgraphEdges(edges)
        sb.append("\t}\n")
    }

    private fun writeSubgraphEdges(edges: List<Pair<String, String>>) {
        edges.map { (a, b) -> "$a -> $b" }.forEach { sb.append("\t\t$it\n") }
    }

    fun finishGraph() {
        sb.append("}")
    }

    fun output() = sb.toString()

    fun writeToFile(out: PrintWriter) {
        out.println(sb.toString())
    }
}
