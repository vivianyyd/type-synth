package query

import util.visualizations.FlowDotWriter
import java.io.File
import java.io.FileOutputStream
import java.io.PrintWriter

fun viz(query: Query, fileName: String = "examples") = ExampleVisualizer(query).viz(fileName)


class ExampleVisualizer(val query: Query) {
    // TODO Wanna graph examples with subexprs or without?

    private val dw = FlowDotWriter()
    private var ctr = 0

    /** Adds the graphviz code that draws [this] node, and returns the name of the graphviz node representing [this]. */
    private fun String.display(): String {
        val gNode = "n${ctr++}"
        dw.writeNode(gNode, this)
        return gNode
    }

    private val inDegrees: MutableMap<String, Int> = query.names.associateWith { 0 }.toMutableMap()
    private val outDegrees: MutableMap<String, Int> = query.names.associateWith { 0 }.toMutableMap()

    private fun visualize(): String {
        dw.startGraph()
        val nodeLabels = query.names.associateWith { it.display() }

        fun Example.leftmostName(): String = when (this) {
            is Name -> this.name
            is App -> this.fn.leftmostName()
        }

        // Not obvious bc some applications could have happened not bc of the fn at the head but bc an argument passed to it allowed the output to be a fn type
        fun edges(app: App): List<Pair<String, String>> {
            val sink = app.leftmostName()
            return app.arg.names.map { src ->
                outDegrees[src] = outDegrees[src]!! + 1
                inDegrees[sink] = inDegrees[sink]!! + 1
                Pair(nodeLabels[src]!!, nodeLabels[sink]!!)
            }
        }

        val allEdges = query.posExsBeforeSubexprs.filterIsInstance<App>().flatMap { edges(it) }.toSet().toList()

        println("In degrees:")
        println(inDegrees)
        println("Out degrees:")
        println(outDegrees)

        dw.writeEdges(allEdges, true, "uses")
        dw.finishGraph()
        val out = dw.output()
        dw.restart()
        return out
    }

    fun writeDotOutput(contents: String, id: String) {
        val out = PrintWriter(FileOutputStream("results${File.separator}$id.dot"))
        out.println(contents)
        out.close()
    }

    fun viz(fileID: String) = writeDotOutput(visualize(), fileID)
}