package symbolicgen.sketcher

import runCommand
import symbolicgen.*
import symbolicgen.Function
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
        "(+ (cons tr []b))" to "lbool",
        "(+ (cons tr (cons tr []b)))" to "lbool",
        "(+ (cons []i [[]]i))" to "llint",
        "(+ (cons []i (cons []i [[]]i)))" to "llint",
        "(- (cons tr []i))" to null,
        "(- (cons []i 0))" to null,
        "(- (cons 0 []b))" to null,
        "(- (cons 0 [[]]i))" to null,
        "(- (cons tr [[]]i))" to null,
        "(- (cons tr (cons 0 []i)))" to null,
    )
    val query = parseNewExamples(consExamples.keys)
    val oracle = ScrappyNewOracle(consExamples.mapKeys { parseNewApp(it.key) })
    val b = SymbolicTypeBuilder(query)
    b.readAllExamples()
    val encoding = EncodeUnrolledUnif(query, b.s, oracle)

    val sketchPath = listOf("src", "main", "sketch", "symbolicgen", "generated").joinToString(
        separator = File.separator, postfix = File.separator
    )
    val sketch = sketchPath + "sketch.sk"
    val sketchOut = sketchPath + "sketchOut.txt"
    fun callSketch(): String {
        return ("sketch $sketch -V 5 --slv-parallel --slv-nativeints --bnd-inline-amnt 5".runCommand())
            ?: throw Exception("I'm sad")
    }

    val out: String
    val runSketch = true
    if (runSketch) {
        File(sketch).printWriter().use { it.println(encoding.make) }
        out = callSketch()
        File(sketchOut).printWriter().use { it.println(out) }
    } else {
        out = File(sketchOut).readText()
    }

    val firstCandidate = Parser.typeAfterSub(Parser.parse(encoding.sk("cons"), out)).constructSketch()

    val nextQuery = encoding.make + "\n" + "harness void neq() { assert (_cons() != $firstCandidate); }"
    File(sketch).printWriter().use { it.println(nextQuery) }
    val newOut = callSketch()
    File(sketchOut).printWriter().use { it.println(newOut) }
    println(Parser.typeAfterSub(Parser.parse(encoding.sk("cons"), newOut)))
}


// TODO make me a class and move me into a separate file
object Parser {
    fun parse(sketchName: String, skOut: String) =
        Parser.blockOfSignature("void $sketchName", skOut).filter { it.contains("=") && !it.contains("_out = root") }
            .associate {
                it.replace("Type@ANONYMOUS ", "").replace("new ", "").split(" = ").let { (lhs, rhs) ->
                    val (t, a) = rhs.split("(")
                    val args = a.replace(")", "")
                    val skTy = when (t) {
                        "Label" -> L
                        "Function" -> {
                            val (l, r) = args.replace("left=", "").replace("rite=", "").split(", ")
                            F(left = N(l), rite = N(r))
                        }
                        "VarBind" -> {
                            val (v, tId) = args.replace("vId=", "").replace("tId=", "").split(", ")
                            VB(vId = v.toInt(), tId = tId.toInt())
                        }
                        "VarRef" -> {
                            val (v, tId) = args.replace("vId=", "").replace("tId=", "").split(", ")
                            VR(vId = v.toInt(), tId = tId.toInt())
                        }
                        "VarLabelBound" -> VL
                        "ConcreteLabel" -> throw Exception("Shouldn't generate types with concrete labels rn")
                        else -> throw Exception("Parsing error")
                    }
                    lhs to skTy
                }
            }

    fun typeAfterSub(l: Map<String, SketchedType>): SketchedType = Parser.sub(l["root"]!!, l)

    private fun sub(t: SketchedType, l: Map<String, SketchedType>): SketchedType = when (t) {
        is N -> Parser.sub(l[t.name]!!, l)
        is L, is VL, is VB, is VR, is CL -> t
        is F -> F(Parser.sub(t.left, l), Parser.sub(t.rite, l))
    }

    private fun blockOfSignature(sig: String, skOut: String): List<String> {
        var txt = skOut.substringAfterLast("$sig (")
        txt = txt.substringAfter('{')
        txt = txt.substringBefore('}')
        return txt.split(';').map { it.trim() }
    }
}

class EncodeUnrolledUnif(val query: NewQuery, private val state: State, private val oracle: EqualityNewOracle) {
    private val w = Writer()

    private var fresh = 0
    private val sketchNames = mutableMapOf<String, String>()

    fun sketchNames(): Map<String, String> = sketchNames

    init {
        query.names.forEach { n ->
            val name = "_${n.filter { it.isLetterOrDigit() }}"
            if (name !in sketchNames.values) sketchNames[n] = name
            else sketchNames[n] = name + "_${fresh++}"
        }
    }

    /** Use me wisely */
    fun sk(name: String) = sketchNames[name]!!  // TODO make me private again once figure out parser infra
    private fun gen(name: String) = "${sk(name)}_gen"
    private val localNumVars = "lVars"

    val make: String by lazy {
        header()
        query.names.forEach { generator(it) }
        query.posExamples.forEach { posExample(it) }
        w.s()
    }

    private fun header() {
        w.include("/home/vivianyyd/type-synth/src/main/sketch/symbolicgen/types.sk")
        w.comment(listOf("NAME\t\tSKETCHNAME\t\tDUMMY") + sketchNames.map { (k, v) ->
            "$k\t\t\t$v\t\t\t${
                if (nullary(k)) oracle.dummy(Name(k)) else ""
            }"
        })
    }

    /** typeId is used to distinguish variables - avoids capture by making their id include which type they're part of */
    private fun choose(portSketchName: String, options: List<SymbolicType>, typeId: Int) {
        val flag = "flag_$portSketchName"
        // TODO not sure if this is right. we didn't see anything that forced us to make this a function so anything but arrow is ok
        val opts = options.ifEmpty { listOf(Variable(), Label()) }
        if (opts.size == 1) {
            pickOption(portSketchName, opts[0], typeId)  // Makes code shorter
            return
        }
        w.lines(
            listOf(
                "int $flag = ??", "assert (${(opts.indices).joinToString(separator = " || ") { "$flag == $it" }})"
            )
        )
        opts.forEachIndexed { i, t ->
            w.block("if ($flag == $i)") { pickOption(portSketchName, t, typeId) }
        }
    }

    private fun pickOption(portSketchName: String, t: SymbolicType, typeId: Int) = when (t) {
        is Label -> w.lines(
            listOf(
                "$portSketchName = new Label()", "canBeBoundInLabel = true"
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
            w.singleLineBlock("if ($vFlag < $localNumVars)", "$portSketchName = new VarRef(vId=$vFlag, tId=$typeId)")
            w.block("else if ($vFlag == $localNumVars)") {
                w.lines(
                    listOf(
                        "$portSketchName = new VarBind(vId=$localNumVars, tId=$typeId)", "$localNumVars++"
                    )
                )
            }
            w.singleLineBlock("else if ($vFlag == $localNumVars + 1)", "$portSketchName = new VarLabelBound()")
            w.line("else assert false")
        }
        is Function -> {
            val leftName = "${portSketchName}l"
            val riteName = "${portSketchName}r"
            w.line("Type $leftName; Type $riteName")
            w.lineComment("input type")
            w.line("canBeFresh = true")
            choose(leftName, t.left, typeId)
            w.lineComment("output type")
            w.line("canBeFresh = false")
            choose(riteName, t.rite, typeId)
            w.line("$portSketchName = new Function(left=$leftName, rite=$riteName)")
        }
        is Error, is Hole -> throw Exception("nah")
    }

    private fun nullary(name: String): Boolean {
        val options = state.read()[name]!!
        return options.size == 1 && options[0] is Label
    }

    var typeId = 0
    private fun generator(name: String) {
        val header = "generator Type ${gen(name)}()"
        if (nullary(name)) w.singleLineBlock(header, "return new ConcreteLabel(dummy=${oracle.dummy(Name(name))})")
        else w.block(header) {
            val options = state.read()[name]!!
            w.lines(
                listOf(
                    "Type root",
                    // TODO canBeFresh need not be in Sketch, it is a property of the tree shape not choices
                    "boolean canBeFresh = false", "boolean canBeBoundInLabel = false", "int $localNumVars = 0"
                )
            )
            w.newLine()
            choose("root", options, typeId++)
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
