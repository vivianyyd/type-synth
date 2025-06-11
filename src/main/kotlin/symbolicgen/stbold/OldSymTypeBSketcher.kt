package symbolicgen.stbold

import query.App
import query.Example
import query.Name
import query.Query
import symbolicgen.sta.*
import symbolicgen.sta.Function
import util.EqualityNewOracle
import util.SketchWriter
import kotlin.math.roundToInt

class OldSymTypeBSketcher(val query: Query, private val state: State, private val oracle: EqualityNewOracle) {
    private val sw = SymbolicSketchWriter()
    fun nextQuery(sketch: String, round: Int) = sw.addBanned(SymbolicSketchParser(sketch).parseAll.first, round)
    fun output(sketch: String): Pair<Int, String> {
        val (types, time) = SymbolicSketchParser(sketch).parseAll
        return time to "${types.mapValues { (_, v) -> v.toString() }}"
    }

    fun readableOutput(sketch: String): String {
        val (time, typesString) = output(sketch)
        return "${time}s\t$typesString"
    }

    fun initialSketch() = sw.make()

    private val sketchNames = mutableMapOf<String, String>()

    /** Use me wisely */
    private fun sk(name: String) = sketchNames[name]!!

    init {
        var fresh = 0
        query.names.forEach { n ->
            val name = "_${n.filter { it.isLetterOrDigit() }}"
            if (name !in sketchNames.values) sketchNames[n] = name
            else sketchNames[n] = name + "_${fresh++}"
        }
    }

    private inner class SymbolicSketchWriter {
        private val w = SketchWriter()

        fun make(): String {
            header()
            query.names.forEach { generator(it) }
            query.posExamples.forEach { posExample(it) }
            return w.s()
        }

        fun addBanned(banned: Map<String, OldSymTypeB>, round: Int): String {
            w.block("harness void banned$round()") {
                w.line(
                    "assert (${
                        banned.map { (n, ty) ->
                            "(${sk(n)}() != ${ty.constructSketch()})"
                        }.joinToString(" || ")
                    })"
                )
            }
            return w.s()
        }

        private fun nullary(name: String): Boolean {
            val options = state.read()[name]!!
            return options.size == 1 && options[0] is Label
        }

        private fun gen(name: String) = "${sk(name)}_gen"
        private val localNumVars = "lVars"

        private fun header() {
            w.include("/home/vivianyyd/type-synth/src/main/sketch/symbolicgen/symbolictypes.sk")
            w.comment(listOf("NAME\t\tSKETCHNAME\t\tDUMMY") + sketchNames.map { (k, v) ->
                "$k\t\t\t$v\t\t\t${
                    if (nullary(k)) oracle.dummy(Name(k)) else ""
                }"
            })
        }

        /** typeId is used to distinguish variables - avoids capture by making their id include which type they're part of */
        private fun chooseFromOptions(portSketchName: String, options: List<SymTypeA>, typeId: Int) {
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

        private fun pickOption(portSketchName: String, t: SymTypeA, typeId: Int): Unit = when (t) {
            is Hole -> {
                val hole = "${portSketchName}_hole"
                w.line("Type $hole")
                w.line("bit ${hole}_flag = ??")
                w.block("if (${hole}_flag)") { pickOption(hole, Label(), typeId) }
                w.block("else") { pickOption(hole, Variable(), typeId) }
                w.line("$portSketchName = $hole")
                // TODO test me!
            }
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

        private var typeId = 0
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
                chooseFromOptions("root", options, typeId++)
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

    private inner class SymbolicSketchParser(private val sketch: String) {
        val parseAll by lazy {
            query.names.associateWith { typeAfterSubs(parseToAssignments(sk(it))) } to (lines.first { "Total time = " in it }
                .substringAfter("Total time = ").toInt() / 1000.0).roundToInt()
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
                            VL(vId = v.toInt(), tId = tId.toInt())
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
            functionsWithWrappers.mapKeys { (k, _) -> k.split(" ")[1] }.filterKeys { it in sketchNames.values }
                .mapValues { (_, v) -> v.filter { it.contains("=") } }
        }

        private val functionsWithWrappers: Map<String, List<String>> by lazy {
            val fns = mutableMapOf<String, MutableList<String>>()
            var fn = false
            var header: String? = null
            lines.forEach {
                if (it == "// FUNCTION START") {
                    fn = true
                    header = null
                } else if (it == "// FUNCTION END") {
                    fn = false
                    header = null
                } else if (fn && header == null) {
                    header = it
                    fns[it] = mutableListOf()
                } else if (fn) {
                    fns[header]!!.add(it.split("//").first().trim())
                }
            }
            fns.mapValues { (_, v) -> v.filter { it.length > 1 } }
        }
    }
}
