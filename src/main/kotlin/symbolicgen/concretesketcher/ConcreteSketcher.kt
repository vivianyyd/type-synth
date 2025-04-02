package symbolicgen.concretesketcher

import symbolicgen.symbolicsketcher.L
import symbolicgen.symbolicsketcher.SpecializedSymbolicType
import util.*

typealias ContextOutline = Map<String, SpecializedSymbolicType>

class ConcreteSketcher(
    val query: NewQuery,
    private val contextOutline: ContextOutline,
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

    private inner class ConcreteSketchWriter {
        private val w = Writer()

        fun make(): String {
            header()
            query.names.forEach { generator(it) }
            query.posExamples.forEach { posExample(it) }
            return w.s()
        }

        private fun nullary(name: String) = contextOutline[name]!! is L

        private fun gen(name: String) = "${sk(name)}_gen"
        private val localNumVars = "lVars"

        private fun header() {
            w.include("/home/vivianyyd/type-synth/src/main/sketch/concretize/concretetypes.sk")
            w.comment(listOf("NAME\t\tSKETCHNAME\t\tDUMMY") + sketchNames.map { (k, v) ->
                "$k\t\t\t$v\t\t\t${
                    if (nullary(k)) oracle.dummy(Name(k)) else ""
                }"
            })
        }

        private fun generator(name: String): Unit {
            /*
            Variables can be fresh or existing
            Make all types, then min(len(register))
            */
            TODO("Think about how to handle VLs")
        }

        private fun obeysOracle(): Unit = TODO("Must match oracle on all pairwise eq/neq")

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

}
