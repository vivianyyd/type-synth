package dependencyanalysis

import util.DependencyGraph
import util.ParameterNode
import util.visualizations.FlowDotWriter
import java.io.File
import java.io.FileOutputStream
import java.io.PrintWriter

fun viz(name: String, da: DependencyAnalysis) = DependencyVisualizer.viz(da.graphs[name]!!, name)

object DependencyVisualizer {
    private var ctr = 0
    private val dw = FlowDotWriter()

    /** Adds the graphviz code that draws [this] node, and returns the name of the graphviz node representing [this]. */
    private fun ParameterNode.display(): String {
        val gNode = "n${ctr++}"
        dw.writeNode(gNode, "${this.f}-${this.i}")
        return gNode
    }

    fun viz(graph: DependencyGraph, fileID: String) = writeDotOutput(visualize(graph), fileID)

    private fun visualize(graph: DependencyGraph): String {
        dw.startGraph()
        val nodeLabels = graph.nodes.associateWith { it.display() }
        dw.writeEdges(graph.deps.map { Pair(nodeLabels[it.sub]!!, nodeLabels[it.sup]!!) }, true, "deps")
        dw.writeEdges(graph.loops.map { Pair(nodeLabels[it.a]!!, nodeLabels[it.a]!!) }, true, "loops")
        dw.finishGraph()
        val out = dw.output()
        dw.restart()
        return out
    }

    fun writeDotOutput(contents: String, id: String) {
        val out = PrintWriter(FileOutputStream("results${File.separator}dep-$id.dot"))
        out.println(contents)
        out.close()
    }
}
