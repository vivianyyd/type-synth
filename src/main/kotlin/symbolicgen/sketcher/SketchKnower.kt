package symbolicgen.sketcher

import symbolicgen.*
import symbolicgen.Function
import test.ConsTest
import util.*

fun main() {
    val query = ConsTest.query
    val oracle = ConsTest.oracle
    val b = SymbolicTypeBuilder(query).make
    val sketcher = SketchKnower(query, b, oracle)

    val runSketch = true
    val out = if (runSketch) callSketch(sketcher.sketchInput(), "test") else readOutput("test")

    println(listOf("_cons_0", "_cons_1", "_cons_2").map { sketcher.parse(it, out) }.joinToString(separator = "\n"))

//    val nextQuery = sketcher.sketchInput() + "\n" + "harness void neq() { assert (_cons() != $firstCandidate); }"
//    File(sketch).printWriter().use { it.println(nextQuery) }
//    val newOut = callSketch()
//    File(sketchOut).printWriter().use { it.println(newOut) }
//    println(sketcher.parse(/*TODO sketcher.sk("cons")*/"_cons", newOut))
}

class SketchKnower(val query: NewQuery, private val state: State, private val oracle: EqualityNewOracle) {
    fun parse(sketchName: String, skOut: String) = SketchParser().parseToType(sketchName, skOut)
    fun sketchInput() = SketchWriter().make

    private val sketchNames = mutableMapOf<String, String>()

    /** Use me wisely */
    private fun sk(name: String) = sketchNames[name]!!
    private var fresh = 0

    init {
        query.names.forEach { n ->
            val name = "_${n.filter { it.isLetterOrDigit() }}"
            if (name !in sketchNames.values) sketchNames[n] = name
            else sketchNames[n] = name + "_${fresh++}"
        }
    }

    private inner class SketchWriter {
        private val w = Writer()

        private fun gen(name: String) = if (nullary(name)) "${sk(name)}_final" else "${sk(name)}_gen"
        private val localNumVars = "lVars"

        val make: String by lazy {
            header()
            query.names.forEach { generator(it) }
            query.posExamples.filterIsInstance<App>().forEach { posExampleAssertions(it) }
            flags()
            harnesses()
            w.s()
        }

        /** An upper bound on the number of candidate contexts for this query. */
        private val rounds: Int by lazy {
            fun <T> List<T>.mapSum(f: (T) -> Int) = this.map(f).fold(0) { a, b -> a + b }

            // TODO we can do something more clever later
            // TODO since we fill in empty lists after tree bulding done, this is not right. empty lists expand to 2
            fun bound(t: SymbolicType): Int = when (t) {
                is Error, is Hole -> throw Exception("shouldn't happen also we'll get rid of this later anyway")
                is Function -> t.left.mapSum(::bound) * t.rite.mapSum(::bound)
                is Label -> 1
                is Variable -> 3
            }
            query.names.map { state.read()[it]!!.mapSum(::bound) }.fold(1) { a, b -> a * b }
        }

        private fun nullary(name: String): Boolean {
            val options = state.read()[name]!!
            return options.size == 1 && options[0] is Label
        }

        private fun header() {
            w.include("/home/vivianyyd/type-synth/src/main/sketch/symbolicgen/types.sk")
            w.comment(listOf("NAME\t\tSKETCHNAME\t\tDUMMY") + sketchNames.map { (k, v) ->
                "$k\t\t\t$v\t\t\t${
                    if (nullary(k)) oracle.dummy(Name(k)) else ""
                }"
            })
        }

        // GENERATORS
        private var typeId = 0
        private fun generator(name: String) {
            if (nullary(name)) {
                w.singleLineBlock("Type ${gen(name)}()", "return new ConcreteLabel(dummy=${oracle.dummy(Name(name))})")
                return
            }
            w.block("generator Type ${gen(name)}()") {
                val options = state.read()[name]!!
                w.lines(
                    listOf(
                        "Type root",
                        // TODO canBeFresh need not be in Sketch, it is a property of the tree shape not choices
                        "boolean canBeFresh = false", "boolean canBeBoundInLabel = false", "int $localNumVars = 0"
                    )
                )
                w.newLine()
                chooseFromOptions("root", options, typeId++)
                w.line("return root")
            }
        }

        /** typeId is used to distinguish variables - avoids capture by making their id include which type they're part of */
        private fun chooseFromOptions(portSketchName: String, options: List<SymbolicType>, typeId: Int) {
            val flag = "flag_$portSketchName"
            // TODO not sure if this is right. we didn't see anything that forced us to make this a function so anything but arrow is ok
            // TODO at the very least this should happen in a pass at the end of Tree building, not here
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
                w.singleLineBlock(
                    "if ($vFlag < $localNumVars)",
                    "$portSketchName = new VarRef(vId=$vFlag, tId=$typeId)"
                )
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
                chooseFromOptions(leftName, t.left, typeId)
                w.lineComment("output type")
                w.line("canBeFresh = false")
                chooseFromOptions(riteName, t.rite, typeId)
                w.line("$portSketchName = new Function(left=$leftName, rite=$riteName)")
            }
            is Error, is Hole -> throw Exception("nah")
        }

        // EXAMPLES
        private fun posExampleAssertions(ex: App) =
            w.block("Type ${assertions(ex)}(Type ${sk(ex.fn)}_t, Type ${sk(ex.arg)}_t)") {
                w.lines(
                    listOf(
                        "assert (isFunction(${sk(ex.fn)}_t))",
                        "Type result = apply((Function)${sk(ex.fn)}_t, ${sk(ex.arg)}_t)",
                        "assert (result != null)",
                        "return result"
                    )
                )
            }

        private fun flags() {
            w.block("generator bit i()") { w.lines(listOf("bit i = ??", "minimize (1 - i)", "return i")) }
            repeat(rounds) { w.singleLineBlock("bit ${flag(it)}", "return i()") }
        }

        private fun harnesses() =
            repeat(rounds) { r -> query.posExamples.forEach { posExample(it, r) } }

        private fun posExample(ex: Example, round: Int) {
            val exRound = exWithRound(ex, round)
            when (ex) {
                is Name -> {
                    if (!nullary(ex.name))
                        w.block("Type $exRound() fixes $exRound") {
                            w.line("Type t = ${gen(ex.name)}()")
                            w.lines((0 until round).map { "assert (t != ${exWithRound(ex, it)}())" })
                            w.line("return t")
                        }
                }
                is App -> w.singleLineBlock(
                    "harness Type $exRound()",
                    "if (${flag(round)}) return ${assertions(ex)}(${
                        exWithRound(ex.fn, round)
                    }(), ${
                        exWithRound(ex.arg, round)
                    }())"
                )
            }
        }


        private fun sk(ex: Example): String = when (ex) {
            is Name -> sk(ex.name)
            is App -> "oo${sk(ex.fn)}co${sk(ex.arg)}cc"
        }

        private fun assertions(ex: App) = sk(ex)

        private fun exWithRound(ex: Example, round: Int) =
            if (ex is Name && nullary(ex.name)) gen(ex.name) else "${sk(ex)}_$round"

        /** Note that this one includes the parens */
        private fun flag(round: Int) = "flag_$round()"

        private inner class Writer {
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
    }

    private inner class SketchParser {
        fun parseToType(sketchName: String, skOut: String) = typeAfterSubs(parseToAssignments(sketchName, skOut))

        // TODO only parse if the output is length more than 3. Then if there's any errors we can just abort
        private fun parseToAssignments(sketchName: String, skOut: String) =
            blockOfSignature("void $sketchName", skOut)
                .filter { it.contains("=") && !it.contains("_out = root") }
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

        private fun typeAfterSubs(l: Map<String, SketchedType>): SketchedType = sub(l["root"]!!, l)

        private fun sub(t: SketchedType, l: Map<String, SketchedType>): SketchedType = when (t) {
            is N -> sub(l[t.name]!!, l)
            is L, is VL, is VB, is VR, is CL -> t
            is F -> F(sub(t.left, l), sub(t.rite, l))
        }

        private fun blockOfSignature(sig: String, skOut: String): List<String> {
            var txt = skOut.substringAfterLast("$sig (")
            txt = txt.substringAfter('{')
            txt = txt.substringBefore('}')
            return txt.split(';').map { it.trim() }
        }
    }
}
