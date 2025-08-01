package concretesketcher

import query.App
import query.Example
import query.Name
import query.Query
import stbold.*
import util.EqualityNewOracle
import util.SketchWriter
import java.lang.Integer.max

typealias ContextOutline = Map<String, OldSymTypeB>

const val TYPE_DEPTH_BOUND = 3

class ConcreteSketcher(
    val query: Query,
    private val contextOutline: ContextOutline,
    private val varTypeIds: Map<String, Int>,
    private val oracle: EqualityNewOracle
) {
    private val sw = ConcreteSketchWriter()
    private val sketchNames = mutableMapOf<String, String>()

    init {
        var fresh = 0
        query.names.forEach { n ->
            val name = "_${n.filter { it.isLetterOrDigit() }}"
            if (name !in sketchNames.values) sketchNames[n] = name
            else sketchNames[n] = name + "_${fresh++}"
        }
    }

    fun query() = sw.make()

    private inner class ConcreteSketchWriter {
        private val w = SketchWriter()

        fun make(): String {
            header()
            query.names.forEach { generator(it) }
            makeAndTest()
            return w.s()
        }

        private fun nullary(name: String) = contextOutline[name]!! is L

        private fun header() {
            w.include("/home/vivianyyd/type-synth/src/main/sketch/concretize/concretetypes.sk")
            w.comment(listOf(
                contextOutline.entries.joinToString(separator = "\n", postfix = "\n"), "NAME\t\tSKETCHNAME\t\tDUMMY"
            ) + sketchNames.map { (k, v) ->
                "$k\t\t\t$v\t\t\t${
                    if (nullary(k)) oracle.dummy(Name(k)) else ""
                }"
            })
        }

        private fun codeFor(t: OldSymTypeB, tid: Int, groundVars: Int, destination: String): Unit =
            when (t) {
                is CL -> w.line("$destination = clabel(register, numLKs, $tid, $groundVars, labelVars, $TYPE_DEPTH_BOUND)")
                L -> w.line("$destination = label(register, numLKs, $tid, $groundVars, labelVars, $TYPE_DEPTH_BOUND)")
                is F -> {
                    val (left, rite) = "${destination}l" to "${destination}r"
                    w.line("Type $left; Type $rite")
                    codeFor(t.left, tid, groundVars, left)
                    codeFor(t.rite, tid, groundVars, rite)
                    w.line("$destination = new Function(left=$left, rite=$rite)")
                }
                is VB -> w.line("$destination = new Variable(tid=${t.tId}, vid=${t.vId})")
                is VR -> w.line("$destination = new Variable(tid=${t.tId}, vid=${t.vId})")
                is VL -> w.line("$destination = variableInLabel(${tid}, $groundVars, labelVars)")
                is N -> throw Exception("rly should fix this")  // TODO
            }

        private fun generator(name: String) {
            val tid = tId(name)
            val outline = outline(name)
            fun lastVar(t: OldSymTypeB): Int = when (t) {
                is F -> max(lastVar(t.left), lastVar(t.rite))
                is CL, L, is VL -> -1
                is VB -> t.vId
                is VR -> t.vId
                is N -> throw Exception("rly should fix this")  // TODO
            }

            val groundVars = lastVar(outline) + 1
            w.block("Type ${sk(name)}(List<LabelKind> register, int numLKs)") {
                w.line("Type root")
                w.line("int labelVars = makeLabelVars()")
                codeFor(outline, tid, groundVars, "root")
                w.line("return root")
            }
        }

        private fun obeysOracle() {
            query.posExamples.forEachIndexed { i, a ->
                query.posExamples.forEachIndexed { j, b ->
                    if (i < j) {
                        if (oracle.equal(a, b)) {
                            w.line("assert(${sk(a)} == ${sk(b)})")
                        } else {
                            w.line("assert(${sk(a)} != ${sk(b)})")
                        }
                    }
                }
            }
        }

        private fun sk(ex: Example): String = when (ex) {
            is Name -> sk(ex.name)
            is App -> "oo${sk(ex.fn)}co${sk(ex.arg)}cc"
        }

        private fun makeAndTest() = w.block("harness void main()") {
            w.lines(listOf(
                "int numLKs",
                "List@list<LabelKind> register = makeLabelKinds(numLKs)"
            ) + query.names.map {
                "Type ${sk(it)} = ${sk(it)}(register, numLKs)"
            })
            w.lines(LinkedHashSet(query.posExamples.filterIsInstance<App>().flatMap { posExample(it) }))
            query.negExamples.filterIsInstance<App>().forEach { negExample(it) }
            obeysOracle()
        }

        private fun posExample(ex: App) = listOf(
            "assert (isFunction(${sk(ex.fn)}))",
            "Type ${sk(ex)} = apply((Function)${sk(ex.fn)}, ${sk(ex.arg)}, true)",
            "assert (${sk(ex)} != null)",
        )

        private fun negExample(ex: App) = w.line(
            "assert (!isFunction(${sk(ex.fn)}) || apply((Function)${sk(ex.fn)}, ${sk(ex.arg)}, false) == null)"
        )
    }

    private inner class ConcreteSketchParser(private val sketch: String) {
//        val parseAll by lazy {
//            query.names.associateWith { typeAfterSubs(parseToAssignments(sk(it))) } to
//                    (lines.first { "Total time = " in it }
//                        .substringAfter("Total time = ").toInt() / 1000.0).roundToInt()
//        }

        val lines = sketch.lines().map { it.replace(";", "").replace("Type@ANONYMOUS", "").trim() }
            .filter { it.isNotEmpty() && it.first() != '@' }

//        // TODO only parse if the output is length more than 3. Then if there's any errors we can just abort
//        private fun parseToAssignments(sketchName: String) =
//            functions[sketchName]!!.filter { it.contains("=") && it.contains("(") }.associate {
//                it.replace("new ", "").split(" = ").let { (lhs, rhs) ->
//                    // TODO make a function that parses args more prettily
//                    val (t, a) = rhs.split("(")
//                    val args = a.replace(")", "")
//                    val skTy = when (t) {
//                        "Label" -> L
//                        "Function" -> {
//                            val (l, r) = args.replace("left=", "").replace("rite=", "").split(", ")
//                            F(left = N(l), rite = N(r))
//                        }
//                        "VarBind" -> {
//                            val (v, tId) = args.replace("vId=", "").replace("tId=", "").split(", ")
//                            VB(vId = v.toInt(), tId = tId.toInt())
//                        }
//                        "VarRef" -> {
//                            val (v, tId) = args.replace("vId=", "").replace("tId=", "").split(", ")
//                            VR(vId = v.toInt(), tId = tId.toInt())
//                        }
//                        "VarLabelBound" -> VL
//                        "ConcreteLabel" -> CL(dummy = args.replace("dummy=", "").toInt())
//                        else -> throw Exception("Parsing error")
//                    }
//                    (if (skTy is CL) "root" else lhs) to skTy
//                }
//            }

//        private fun typeAfterSubs(l: Map<String, SpecializedSymbolicType>): SpecializedSymbolicType =
//            sub(l["root"]!!, l)

//        private fun sub(t: SpecializedSymbolicType, l: Map<String, SpecializedSymbolicType>): SpecializedSymbolicType =
//            when (t) {
//                is N -> sub(l[t.name]!!, l)
//                is L, is VL, is VB, is VR, is CL -> t
//                is F -> F(sub(t.left, l), sub(t.rite, l))
//            }

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

//    fun output(sketch: String): Pair<Int, String> {
//        val (types, time) = ConcreteSketchParser(sketch).parseAll
//        return time to "${types.mapValues { (_, v) -> v.toString() }}"
//    }

//    fun readableOutput(sketch: String): String {
//        val (time, typesString) = output(sketch)
//        return "${time}s\t$typesString"
//    }

    fun makeSketch() = sw.make()

    /** Use me wisely */
    private fun sk(name: String) = sketchNames[name]!!
    private fun outline(name: String) = contextOutline[name]!!
    private fun tId(name: String) = varTypeIds[name]!!
}
