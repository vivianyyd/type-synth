package symbolicgen

import runCommand
import util.*
import java.io.File

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
    val oracle = ScrappyNewOracle(consExamples.mapKeys { parseNewApp(it.key) })
    val b = SymbolicTypeBuilder(query)
    b.readAllExamples()
    val encoding = EncodeUnrolledUnif(query, b.s, oracle)

    val sketchPath = listOf("src", "main", "sketch", "symbolicgen", "generated").joinToString(
        separator = File.separator,
        postfix = File.separator
    )
    val sketch = sketchPath + "sketch.sk"
    val sketchOut = sketchPath + "sketchOut.txt"
    File(sketch).printWriter().use { out -> out.println(encoding.make()) }

    fun callSketch(): String {
        return ("sketch $sketch -V 5 --slv-parallel --slv-nativeints --bnd-inline-amnt 5".runCommand())
            ?: throw Exception("I'm sad")
    }

    fun blockOfSignature(sig: String, skOut: String): List<String> {
        var txt = skOut.substringAfterLast("$sig (")
        txt = txt.substringAfter('{')
        txt = txt.substringBefore('}')
        return txt.split(';').map { it.trim() }
    }

    val out = callSketch()
    File(sketchOut).printWriter().use { it.println(out) }
    println(blockOfSignature("void _cons", out).joinToString(separator = "\n"))
}

class EncodeUnrolledUnif(val query: NewQuery, private val state: State, private val oracle: EqualityNewOracle) {
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
    private val localNumVars = "lVars"
    private val globalNumVars = "gVars"

    fun make(): String {
        header()
        query.names.forEach { generator(it) }
        query.posExamples.forEach { posExample(it) }
        return w.s()
    }

    private fun header() {
        w.include("/home/vivianyyd/type-synth/src/main/sketch/symbolicgen/types.sk")
        w.comment(listOf("NAME\t\tSKETCHNAME\t\tDUMMY") + sketchNames.map { (k, v) ->
            "$k\t\t\t$v\t\t\t${
                if (nullary(k)) oracle.dummy(Name(k)) else ""
            }"
        })
        w.line("int $globalNumVars = 0")
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
        is Variable -> {
            val vFlag = "v_$portSketchName"
            w.lines(
                listOf(
                    "int $vFlag = ??",
                    "assert ($vFlag >= 0 && $vFlag < $localNumVars + 2)",
                    "if (!canBeFresh) assert ($vFlag != $localNumVars)",
                    "if (!canBeBoundInLabel) assert ($vFlag != $localNumVars + 1)"
                )
            )
            w.block("if ($vFlag < $localNumVars)") {
                w.line("$portSketchName = new VarRef(id=$vFlag + $globalNumVars)")
            }
            w.block("else if ($vFlag == $localNumVars)") {
                w.lines(
                    listOf(
                        "$portSketchName = new VarBind(id=$localNumVars + $globalNumVars)",
                        "$localNumVars++"
                    )
                )
            }
            w.block("else if ($vFlag == $localNumVars + 1)") { w.line("$portSketchName = new VarLabelBound()") }
            w.line("else assert false")
        }
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

    private fun nullary(name: String): Boolean {
        val options = state.read()[name]!!
        return options.size == 1 && options[0] is Label
    }

    private fun generator(name: String) {
        val header = "generator Type ${gen(name)}()"
        if (nullary(name)) w.singleLineBlock(header, "return new ConcreteLabel(dummy=${oracle.dummy(Name(name))})")
        else
            w.block(header) {
                val options = state.read()[name]!!
                w.lines(
                    listOf(
                        "Type root",
                        // TODO canBeFresh need not be in Sketch, it is a property of the tree shape not choices
                        "boolean canBeFresh = false",
                        "boolean canBeBoundInLabel = false",
                        "int $localNumVars = 0"
                    )
                )
                w.newLine()
                choose("root", options)
                w.line("$globalNumVars += $localNumVars")
                w.line("return root")
            }
    }

    private fun sk(ex: Example): String = when (ex) {
        is Name -> sk(ex.name)
        is App -> "oo${sk(ex.fn)}co${sk(ex.arg)}cc"
    }

    private fun posExample(ex: Example) = when (ex) {
        is Name -> w.singleLineBlock("harness Type ${sk(ex)}()", "return ${gen(ex.name)}()")
        is App -> w.block("harness Type ${sk(ex)}()") {
            w.lines(
                listOf(
                    "assert (isFunction(${sk(ex.fn)}()))",
                    "Type result = apply((Function)${sk(ex.fn)}(), ${sk(ex.arg)}())",
                    "assert (result != null)",
                    "return result"
                )
            )
        }
    }
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

    fun singleLineBlock(header: String, l: String) = lineNoSemi("$header { $l; }")

    fun s() = sb.toString()
}
