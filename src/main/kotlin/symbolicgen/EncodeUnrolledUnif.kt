package symbolicgen

import util.NewQuery
import java.io.File

fun main() {
    val sketchPath = listOf("src", "main", "sketch", "symbolicgen", "generated").joinToString(
        separator = File.separator,
        postfix = File.separator
    )
//    val out = PrintWriter(FileOutputStream(sketchPath + "scratchpad.sk"))
//    out.println("hello")
//    out.close()
    EncodeUnrolledUnif(NewQuery(names = listOf("a[]", "!b", "c1")), State(NewQuery())).make()
}

class EncodeUnrolledUnif(val query: NewQuery, val state: State) {
    private val w = Writer()

    private var fresh = 0
    private val sketchNames = query.names.associateWith { n -> "_${n.filter { it.isLetterOrDigit() }}-${fresh++}" }

    /** Use me wisely */
    fun sk(name: String) = sketchNames[name]!!

    fun make() {
        header()
        query.names.forEach { generator(it) }
        println(w.s()) // TODO
    }

    private fun header() {
        w.line("include \"/home/vivianyyd/type-synth/src/main/sketch/symbolicgen/types.sk\";")
        w.comment(listOf("NAME\t\tDUMMY") + sketchNames.map { (k, v) -> "$k\t\t\t$v" })
    }

    private fun generator(name: String) {
        w.line("generator Type ${sk(name)}Gen() {")
        w.indent()

        // TODO how to encode tree as Sketch choices
        // TODO First just do the whole tree and see how it goes. Probably bad.
        //      Then do variable bindings. Hope it just works, and constraints I do explicitly are implicit in Sketch.
        //      If not, then see if we need to explicitly help it number the nodes and make constraints for itself
        //      For variable binding reasoning, could give each V/L an id field so we can refer to them
        //        Actually even better - since we construct them nestedly, each V field can just store pointers or inds
        //        of nodes that could've bound them
        //        But how does that help? Need to use that info in example checker algo

        w.dedent()
        w.line("}")
    }

    /*
    generator calls for each name (microopt that might be unnecessary: if only one choice, short circuit to directly produce it)

    for each example, hard-code how to unify it:
    order all examples by subexpressions
    TODO what's the most efficient way to memoize computations in sketch?

    type-expr-dummy-name... type-expr-dummy-name
        they are functions that call the generator dummies
    and they call each other for subexpr references

    TODO how to deal with variable bindings?

    CHECK cons 0 []i
        CHECK cons 0
            CHECK cons
            ASSERT cons is ->
            CHECK 0
            ASSERT 0 < cons param type
        ASSERT cons 0 is ->
        CHECK []i
        ASSERT []i < cons 0 param type
     */
}

class Writer {
    private val sb = StringBuilder()
    private var indentLevel = 0

    fun indent() = indentLevel++
    fun dedent() = indentLevel--

    fun line(l: String) {
        repeat(indentLevel) { sb.append("\t") }
        sb.appendLine(l)
    }

    fun lines(l: List<String>) = l.forEach { line(it) }

    fun comment(l: List<String>) {
        line("/*")
        lines(l)
        line("*/")
    }

    fun s() = sb.toString()
}
