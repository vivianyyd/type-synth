package stbold

import query.App
import query.Example
import query.Name
import query.Query
import sta.Function
import sta.State
import util.EqualityNewOracle
import kotlin.math.roundToInt

// TODO style: can inline tests into the harness that wraps all the tests
class OldSymTypeBSketcherUsingFixes(
    val query: Query,
    private val state: State,
    private val oracle: EqualityNewOracle,
    private val rounds: Int? = null
) {
    fun parse(skOut: String) = SketchParser(skOut).parseAll
    fun sketchInput() = SketchWriter(rounds).make

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

    private inner class SketchWriter(rounds: Int? = null) {
        private val w = Writer()

        private fun gen(name: String) = if (nullary(name)) "${sk(name)}_final" else "${sk(name)}_gen"
        private val localNumVars = "lVars"

        /** An upper bound on the number of candidate contexts for this query. */
        private val rounds: Int by lazy {
            if (rounds != null) rounds else {
                fun <T> List<T>.mapSum(f: (T) -> Int) = this.map(f).fold(0) { a, b -> a + b }
                fun bound(t: sta.SymTypeA): Int = when (t) {
                    is Function -> t.left.mapSum(::bound) * t.rite.mapSum(::bound)
                    is sta.Label -> 1
                    is sta.Variable -> 3
                    is sta.Hole -> 4
                }
                query.names.map { state.read()[it]!!.mapSum(::bound) }.fold(1) { a, b -> a * b }
            }
        }

        val make: String by lazy {
            println("$rounds ROUNDS")

            header()
            query.names.forEach { generator(it) }
            query.posExamples.filterIsInstance<App>().forEach { posExampleAssertions(it) }
            flags()
            harnesses()
            w.s()
        }

        private fun nullary(name: String): Boolean {
            val options = state.read()[name]!!
            return options.size == 1 && options[0] is sta.Label
        }

        private fun header() {
            w.include("/home/vivianyyd/type-synth/src/main/sketch/symbolicgen/symbolictypes.sk")
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
                w.singleLineBlock(
                    "Type ${gen(name)}() fixes ${gen(name)}",
                    "return new ConcreteLabel(dummy=${oracle.dummy(Name(name))})"
                )
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
        private fun chooseFromOptions(portSketchName: String, options: List<sta.SymTypeA>, typeId: Int) {
            val flag = "flag_$portSketchName"
            if (options.size == 1) {
                pickOption(portSketchName, options[0], typeId)  // Makes code shorter
                return
            }
            w.lines(
                listOf(
                    "int $flag = ??",
                    "assert (${(options.indices).joinToString(separator = " || ") { "$flag == $it" }})"
                )
            )
            options.forEachIndexed { i, t ->
                w.block("if ($flag == $i)") { pickOption(portSketchName, t, typeId) }
            }
        }

        private fun pickOption(portSketchName: String, t: sta.SymTypeA, typeId: Int): Unit = when (t) {
            is sta.Hole -> {
                val hole = "${portSketchName}_hole"
                w.line("Type $hole")
                w.line("bit ${hole}_flag = ??")
                w.block("if (${hole}_flag)") { pickOption(hole, sta.Label(), typeId) }
                w.block("else") { pickOption(hole, sta.Variable(), typeId) }
                w.line("$portSketchName = $hole")
                // TODO test me!
            }
            is sta.Label -> w.lines(
                listOf(
                    "$portSketchName = new Label()", "canBeBoundInLabel = true"
                )
            )
            is sta.Variable -> {
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
                    "if ($vFlag < $localNumVars)", "$portSketchName = new VarRef(vId=$vFlag, tId=$typeId)"
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
            // This doesn't seem to actually make generation any faster. So TODO removeme?
            w.block("harness void dontEvenTry()") {
                (0 until rounds - 1).forEach { f ->
                    w.singleLineBlock(
                        "if (!${flag(f)})",
                        "assert (${(f + 1 until rounds).joinToString(separator = " && ") { "!${flag(it)}" }})"
                    )
                }
            }
        }

        private fun harnesses() {
            repeat(rounds) { r ->
                query.posExamples.forEach { posExample(it, r) }
                w.block("harness void EXAMPLE_WRAPPER_$r()") {
                    w.block("if (${flag(r)})") {
                        w.lines((0 until r).map {
                            "assert (${flag(it)})"
                        })
                        w.lines(query.posExamples.flatMap { ex ->
                            if (ex is Name && !nullary(ex.name)) {
                                (0 until r).map {
                                    "assert (!eq(${exWithRound(ex, r)}(), ${exWithRound(ex, it)}()))"
                                }
                            } else listOf("${exWithRound(ex, r)}()")
                        })
                    }
                }
            }
        }

        private fun posExample(ex: Example, round: Int) {
            val exRound = exWithRound(ex, round)
            when (ex) {
                is Name -> {
                    if (!nullary(ex.name)) w.block("Type $exRound() fixes $exRound") {
                        w.line("return ${gen(ex.name)}()")
                    }
                }
                is App -> w.singleLineBlock(
                    "Type $exRound()", "return ${assertions(ex)}(${
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
            if (ex is Name && nullary(ex.name)) gen(ex.name) else "${sk(ex)}_ROUND$round"

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

    private inner class SketchParser(private val sketch: String) {
        val parseAll by lazy {
            functions.keys.associateWith { parseToAssignments(it) }
                .filter { (_, v) -> v.isNotEmpty() }
                .mapValues { (_, v) -> typeAfterSubs(v) } to
                    (lines.first { "Total time = " in it }
                        .substringAfter("Total time = ")
                        .toInt() / 1000.0).roundToInt()
        }

        val lines = sketch.lines().map { it.replace(";", "").replace("Type@ANONYMOUS", "").trim() }
            .filter { it.isNotEmpty() && it.first() != '@' }

        // TODO only parse if the output is length more than 3. Then if there's any errors we can just abort
        private fun parseToAssignments(sketchName: String) =
            functions[sketchName]!!.filter { it.contains("=") && it.contains("(") }.associate {
                it.replace("new ", "").split(" = ").let { (lhs, rhs) ->
                    // TODO make a function that parses args more prettily
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
                        "VarLabelBound" -> {
                            val (v, tId) = args.replace("vId=", "").replace("tId=", "").split(", ")
                            VR(vId = v.toInt(), tId = tId.toInt())
                        }
                        "ConcreteLabel" -> CL(dummy = args.replace("dummy=", "").toInt())
                        else -> throw Exception("Parsing error")
                    }
                    (if (skTy is CL) "root" else lhs) to skTy
                }
            }

        private fun typeAfterSubs(l: Map<String, OldSymTypeB>): OldSymTypeB =
            sub(l["root"]!!, l)

        private fun sub(t: OldSymTypeB, l: Map<String, OldSymTypeB>): OldSymTypeB =
            when (t) {
                is N -> sub(l[t.name]!!, l)
                is L, is VL, is VB, is VR, is CL -> t
                is F -> F(sub(t.left, l), sub(t.rite, l))
            }

        private fun blockOfSignature(sig: String): List<String> {
            var txt = sketch.substringAfterLast("$sig (")
            txt = txt.substringAfter('{')
            txt = txt.substringBefore('}')
            return txt.split(';').map { it.trim() }
        }

        private val functions: Map<String, List<String>> by lazy {
            functionsFirstPass.mapKeys { (k, _) -> k.split(" ")[1] }
                .mapValues { (_, v) -> v.filter { it.contains("=") } }
        }

        private val functionsFirstPass: Map<String, List<String>> by lazy {
            val fns = mutableMapOf<String, MutableList<String>>()
            var fn = false
            var header: String? = null
            lines.forEach {
                if (it.contains("  fixes  ")) {
                    fn = true
                    header = it
                    fns[it] = mutableListOf()
                } else if (it == "// FUNCTION END") {
                    fn = false
                    header = null
                } else if (fn) {
                    fns[header]!!.add(it.split("//").first().trim())
                }
            }
            fns.mapValues { (_, v) -> v.filter { it.length > 1 } }
        }
    }
}
