package symbolicgen

import symbolicgen.concretesketcher.ContextOutline
import util.EqualityNewOracle
import util.NewQuery

sealed interface ConstrainedType
sealed interface ConcreteType : ConstrainedType
class ConsLHole(val options: MutableList<ConcreteType> = mutableListOf(), val constraint: DependencyConstraint?) :
    ConstrainedType

class ConcCL(val dummy: Int) : ConstrainedType


class ConcL(val l: Int, val params: List<ConcreteType>) : ConcreteType
class ConcF(val left: ConstrainedType, val rite: ConstrainedType) : ConcreteType
class ConcVB(val vid: Int, val tid: Int) : ConcreteType
class ConcVR(val vid: Int, val tid: Int) : ConcreteType
class ConcVL(val vid: Int, val tid: Int) : ConcreteType

class ConcreteEnumerator(
    val query: NewQuery,
    private val contextOutline: ContextOutline,
    private val dependencies: DependencyAnalysis,
    private val varTypeIds: Map<String, Int>,
    private val oracle: EqualityNewOracle
) {
    init {
        contextOutline.forEach { (name, outline) ->
            val paramIndex = 0
            val constraints = dependencies.constraints(name)

        }

    }

//        val constraint = when (val c = constraints[paramIndex]) {
//            null -> "null"
//            is ContainsNoVariables -> "new NoVars()"
//            is ContainsOnly -> "new OnlyVariable(tid=${c.tId}, vid=${c.vId})"
//        }
//        when (t) {
//            is CL -> w.line("$destination = clabel(register, numLKs, $tid, $groundVars, $constraint, $TYPE_DEPTH_BOUND)")
//            L -> w.line("$destination = label(register, numLKs, $tid, $groundVars, labelVars, $constraint, $TYPE_DEPTH_BOUND)")
//            is F -> {
//                val (left, rite) = "${destination}l" to "${destination}r"
//                w.line("Type $left; Type $rite")
//                codeFor(t.left, tid, groundVars, left, constraints, paramIndex)
//                codeFor(t.rite, tid, groundVars, rite, constraints, paramIndex + 1)
//                w.line("$destination = new Function(left=$left, rite=$rite)")
//            }
//            is VB -> w.line("$destination = new Variable(tid=${t.tId}, vid=${t.vId})")
//            is VR -> w.line("$destination = new Variable(tid=${t.tId}, vid=${t.vId})")
//            is VL -> w.line("$destination = variableInLabel(${tid}, $groundVars, labelVars)")
//            is N -> throw Exception("rly should fix this")  // TODO
//        }
//
//        private fun generator(name: String) {
//            val tid = tId(name)
//            val outline = outline(name)
//            fun lastVar(t: SpecializedSymbolicType): Int = when (t) {
//                is F -> max(lastVar(t.left), lastVar(t.rite))
//                is CL, L, is VL -> -1
//                is VB -> t.vId
//                is VR -> t.vId
//                is N -> throw Exception("rly should fix this")  // TODO
//            }
//
//            val groundVars = lastVar(outline) + 1
//            w.block("Type ${sk(name)}(LabelKind[8] register, int numLKs)") {
//                w.line("Type root")
//                if (!nullary(name)) w.line("int labelVars = makeLabelVars()")
//                codeFor(outline, tid, groundVars, "root", dependencies.constraints(name), 0)
//                w.line("return root")
//            }
//        }
//
//        private fun obeysOracle() {
//            query.posExamples.forEachIndexed { i, a ->
//                query.posExamples.forEachIndexed { j, b ->
//                    if (i < j) {
//                        if (oracle.equal(a, b)) {
//                            w.line("assert(${sk(a)} == ${sk(b)})")
//                        } else {
//                            w.line("assert(${sk(a)} != ${sk(b)})")
//                        }
//                    }
//                }
//            }
//        }
//
//        private fun sk(ex: Example): String = when (ex) {
//            is Name -> sk(ex.name)
//            is App -> "oo${sk(ex.fn)}co${sk(ex.arg)}cc"
//        }
//
//        private fun makeAndTest() = w.block("harness void main()") {
//            w.lines(listOf(
//                "int numLKs",
//                "LabelKind[8] register = makeLabelKinds(numLKs)"
//            ) + query.names.map {
//                "Type ${sk(it)} = ${sk(it)}(register, numLKs)"
//            })
//            w.lines(LinkedHashSet(query.posExamples.filterIsInstance<App>().flatMap { posExample(it) }))
//            query.negExamples.filterIsInstance<App>().forEach { negExample(it) }
//            obeysOracle()
//        }
//
//        private fun posExample(ex: App) = listOf(
//            "assert (isFunction(${sk(ex.fn)}))",
//            "Type ${sk(ex)} = apply((Function)${sk(ex.fn)}, ${sk(ex.arg)}, true)",
//            "assert (${sk(ex)} != null)",
//        )
//
//        private fun negExample(ex: App) = w.line(
//            "assert (!isFunction(${sk(ex.fn)}) || apply((Function)${sk(ex.fn)}, ${sk(ex.arg)}, false) == null)"
//        )
//    }
}
