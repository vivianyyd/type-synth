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

    open fun line(l: String) = lineNoSemi(l)

    fun lines(l: Collection<String>) = l.forEach { line(it) }
}

class PyWriter : Writer() {
    fun comment(l: String) = line("# $l")

    fun import(l: String) {
        line("from $l import *")
    }

    fun beginMain() {
        line("if __name__ == '__main__':")
        indent()
    }

    fun query(header: String, decls: List<String>, constrs: List<String>): String {
        comment(header)
        import("cvc5.pythonic")
        import("cardinality")
        beginMain()

        decls.forEach { line(it) }
        line("solve(")
        indent()
        lines(constrs.map { "$it," })
        dedent()
        line(")")
        return sb.toString()
    }
}

class SketchWriter : Writer() {
    override fun line(l: String) = lineNoSemi("$l;")

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
