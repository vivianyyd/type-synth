package util

sealed class Writer {
    protected val sb = StringBuilder()
    private var indentLevel = 0

    fun indent() = indentLevel++
    fun dedent() = indentLevel--

    fun newLine() = sb.appendLine()

    protected fun lineNoSemi(l: String) {
        repeat(indentLevel) { sb.append("\t") }
        sb.appendLine(l)
    }

    abstract fun line(l: String)
    abstract fun lines(l: Collection<String>)
}

class PyWriter : Writer() {
    private val decls = mutableListOf<String>()
    private val constrs = mutableListOf<String>()

    override fun line(l: String) = lineNoSemi(l)

    override fun lines(l: Collection<String>) = l.forEach { line(it) }

    fun import(l: String) {
        line("from $l import *")
    }

    fun beginMain() {
        line("if __name__ == '__main__':")
        indent()
    }

    fun decls(d: List<String>) = decls.addAll(d)

    fun constrs(c: List<String>) = constrs.addAll(c)

    fun s(): String {
        decls.forEach { line(it) }
        line("solve(")
        indent()
        line(constrs.joinToString(separator = ",\n"))
        dedent()
        line(")")
        return sb.toString()
    }
}

class SketchWriter : Writer() {
    override fun line(l: String) = lineNoSemi("$l;")

    override fun lines(l: Collection<String>) = l.forEach { line(it) }

    fun include(l: String) {
        line("include \"$l\"")
    }

    fun lineComment(l: String) = lineNoSemi("// $l")

    fun comment(l: List<String>) {
        lineNoSemi("/*")
        l.forEach { lineNoSemi(it) }
        lineNoSemi("*/")
    }

    fun block(header: String, buildBody: () -> Unit) {
        lineNoSemi("$header {")
        indent()
        buildBody()
        dedent()
        lineNoSemi("}")
    }

    fun singleLineBlock(header: String, l: String) = lineNoSemi("$header { $l; }")

    fun s() = sb.toString()
}
