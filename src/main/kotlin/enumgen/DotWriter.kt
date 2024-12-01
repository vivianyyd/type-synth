package enumgen

import java.io.PrintWriter

class DotWriter {
    private val sb = StringBuilder()

    fun startGraph() {
        sb.append("digraph g {")
        sb.appendLine()
        listOf(
            "splines=false;",
            "rankdir=TD; ordering=out;",
            "node [shape = record, height=.1];"
        ).forEach { sb.append("\t$it\n") }
    }

    fun writeNode(nodeName: String, label: String) {
        sb.append("\t$nodeName [label = \"$label\"];\n")
    }

    fun writeLangNode(fnNames: List<String>) =
        writeNode(
            "root",
            "{ L | { ${fnNames.joinToString(separator = " | ")} } }"
        )

    fun writeTypeNode(nodeName: String, type: String, ports: List<String>) =
        if (ports.isEmpty()) writeNode(nodeName, type)
        else writeNode(
            nodeName,
            "{ $type | { ${ports.joinToString(separator = " | ") { "<$it>" }} } }"
        )

    fun writeEdge(sourceName: String, sinkName: String) =
        sb.append("\t$sourceName:s -> $sinkName:n;\n")

    fun finishGraph() {
        sb.append("}")
    }

    fun output() = sb.toString()

    fun writeToFile(out: PrintWriter) {
        out.println(sb.toString())
    }
}
