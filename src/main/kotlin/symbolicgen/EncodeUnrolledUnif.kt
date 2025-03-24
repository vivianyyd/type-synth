package symbolicgen

import util.*
import java.io.File
import java.io.FileOutputStream
import java.io.PrintWriter

fun main() {
    val consExamples = mapOf(
        "(+ 0)" to "int",
        "(+ tr)" to "bool",
        "(+ []i)" to "lint",
        "(+ []b)" to "lbool",
        "(+ [[]]i)" to "llint",
        "(+ (cons 0))" to "lint to lint",
        "(+ (cons 0 []i))" to "lint",
        "(+ (cons 0 (cons 0 []i)))" to "lint",
//        "(+ (cons tr []b))" to "lbool",
//        "(+ (cons tr (cons tr []b)))" to "lbool",
//        "(+ (cons []i [[]]i))" to "llint",
//        "(+ (cons []i (cons []i [[]]i)))" to "llint",
//        "(- (cons tr []i))" to null,
//        "(- (cons []i 0))" to null,
//        "(- (cons 0 []b))" to null,
//        "(- (cons 0 [[]]i))" to null,
//        "(- (cons tr [[]]i))" to null,
//        "(- (cons tr (cons 0 []i)))" to null,
    )
    val query = parseNewExamples(consExamples.keys)
    val b = SymbolicTypeBuilder(query)
    b.readAllExamples()
    val encoding = EncodeUnrolledUnif(query, b.s)

    val sketchPath = listOf("src", "main", "sketch", "symbolicgen", "generated").joinToString(
        separator = File.separator,
        postfix = File.separator
    )
    val out = PrintWriter(FileOutputStream(sketchPath + "scratchpad.sk"))
    out.println(encoding.make())
    out.close()
}

class EncodeUnrolledUnif(val query: NewQuery, val state: State) {
    private val w = Writer()

    private var fresh = 0
    private val sketchNames = mutableMapOf<String, String>()

    init {
        query.names.forEach { n ->
            val name = "_${n.filter { it.isLetterOrDigit() }}"
            if (name !in sketchNames.values) sketchNames[n] = name
            else sketchNames[n] = name + "_${fresh++}"
        }
    }

    /** Use me wisely */
    private fun sk(name: String) = sketchNames[name]!!
    private fun gen(name: String) = "${sk(name)}_gen"

    fun make(): String {
        header()
        query.names.forEach { generator(it) }
        query.posExamples.forEach { posExample(it) }
        return w.s()
    }

    private fun header() {
        w.include("/home/vivianyyd/type-synth/src/main/sketch/symbolicgen/types.sk")
        w.include("/home/vivianyyd/applications/sketch-1.7.6/sketch-frontend/sketchlib/list.skh")
        w.comment(listOf("NAME\t\tDUMMY") + sketchNames.map { (k, v) -> "$k\t\t\t$v" })
    }

    private fun choose(portSketchName: String, options: List<SymbolicType>) {
        val flag = "flag_$portSketchName"
        // TODO not sure if this is right. we didn't see anything that forced us to make this a function so anything but arrow is ok
        val opts = options.ifEmpty { listOf(Variable(), Label()) }
        if (opts.size == 1) {
            pickOption(portSketchName, opts[0])  // Makes code shorter
            return
        }
        w.lines(
            listOf(
                "int $flag = ??",
                "assert (${(opts.indices).joinToString(separator = " || ") { "$flag == $it" }})"
            )
        )
        opts.forEachIndexed { i, t ->
            w.block("if ($flag == $i)") { pickOption(portSketchName, t) }
        }
    }

    private fun pickOption(portSketchName: String, t: SymbolicType) = when (t) {
        is Label -> w.lines(
            listOf(
                "$portSketchName = new Label()",
                "canBeBoundInLabel = true"
            )
        )
        is Variable -> w.lines(
            listOf(
                "List<int> bindings",
                "if (!(canBeFresh || canBeBoundInLabel)) bindings = vars",
                "$portSketchName = new Var(id=varId, possBindings=bindings)",
                "vars = add(vars, varId)",
                "varId++",
            )
        )
        is Function -> {
            val leftName = "${portSketchName}l"
            val riteName = "${portSketchName}r"
            w.line("Type $leftName; Type $riteName")
            w.lineComment("input type")
            w.line("canBeFresh = true")
            choose(leftName, t.left)
            w.lineComment("output type")
            w.line("canBeFresh = false")
            choose(riteName, t.rite)
            w.line("$portSketchName = new Function(left=$leftName, rite=$riteName)")
        }
        is Error, is Hole -> throw Exception("nah")
    }

    private fun generator(name: String) =
        w.block("generator Type ${gen(name)}()") {
            val options = state.read()[name]!!
            if (options.size == 1 && options[0] is Label) w.line("return new Label()")  // Makes code shorter
            else {
                w.lines(
                    listOf(
                        "Type root",
                        "boolean canBeFresh = false",
                        "boolean canBeBoundInLabel = false",
                        "int varId = 0",
                        "List<int> vars = empty()"
                    )
                )
                w.newLine()
                choose("root", options)
                w.line("return root")
            }
        }

    private fun exToSketch(ex: Example): String = when (ex) {
        is Name -> sk(ex.name)
        is App -> "oo${exToSketch(ex.fn)}co${exToSketch(ex.arg)}cc"
    }

    private fun posExample(ex: Example) = when (ex) {
        is Name -> w.block("harness Type ${exToSketch(ex)}()") { w.line("return ${gen(ex.name)}()") }
        is App -> w.block("harness Type ${exToSketch(ex)}()") {
            w.lines(
                listOf(
                    "assert (isFunction(${exToSketch(ex.fn)}()))",
                    "assert (leq(${exToSketch(ex.arg)}(), ((Function)${exToSketch(ex.fn)}()).left))",
                    // TODO Here we compute possible variable bindings performed by zero.
                    //  A Var must store things it could be bound by. Then in leq we can reason about possible binders
                    "return ((Function)${exToSketch(ex.fn)}()).rite"
                )
            )
        }
    }

    // TODO Then we can have an Array<Type> of dynamic size = whatever the counter ended at after picking types
    //  which stores what the mappings are
    //  what about variable capture or something in (cons 0) (cons 0) when we say a == b or c.. should we make varIds fresh over all types
    //      Checking an example:
    //          If possbinders is NULL (vs empty?) it passes like a freshVar
    //          Check if SAT that arg passed to V is equal to any of V's possible binders
    //          (as we read args, bind vars to them to refer to later when we check possible var equality.
    //          Could iterate down type/thru list of bindings and keep a map)
    //          Not trivial - Need to know what a is bound to in (a->b)->a
    //      No need to explicitly write choice => Label if Var always UNSAT!
    //      Add typeEq oracle with dummies for values, like how I handled len in s4s
    //      Try: encode variable bindings/equality => are constraints I do explicitly implicit in Sketch?
    //      If doesn't work, see if can explicitly make constraints
}

class Writer {
    private val sb = StringBuilder()
    private var indentLevel = 0

    fun indent() = indentLevel++
    fun dedent() = indentLevel--

    fun newLine() = sb.appendLine()

    fun line(l: String) = lineNoSemi("$l;")

    private fun lineNoSemi(l: String) {
        repeat(indentLevel) { sb.append("\t") }
        sb.appendLine(l)
    }

    fun lines(l: List<String>) = l.forEach { line(it) }

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

    fun s() = sb.toString()
}
