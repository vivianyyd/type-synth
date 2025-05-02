package symbolicgen.concreteenumerator

import symbolicgen.DependencyAnalysis
import symbolicgen.DependencyConstraint
import symbolicgen.concretesketcher.ContextOutline
import symbolicgen.symbolicsketcher.*
import symbolicgen.symbolicsketcher.F
import symbolicgen.symbolicsketcher.L
import util.EqualityNewOracle
import util.Query

val labels = mapOf(0 to 1, 1 to 0, 2 to 0)

class Root(val options: MutableList<ConstrainedType> = mutableListOf())
sealed interface ConstrainedType
sealed interface ConcreteType : ConstrainedType
class Hole() : ConstrainedType
class L(
    val label: Int,
    val ports: MutableList<MutableList<ConstrainedType>> = mutableListOf(),
    val constraint: DependencyConstraint?
) : ConstrainedType

class F(val left: MutableList<ConstrainedType>, val rite: MutableList<ConstrainedType>) : ConcreteType
data class ConcVB(val vid: Int, val tid: Int) : ConcreteType
data class ConcVR(val vid: Int, val tid: Int) : ConcreteType
data class ConcVL(val vid: Int, val tid: Int) : ConcreteType

class ConcreteEnumerator(
    val query: Query,
    private val contextOutline: ContextOutline,
    private val dependencies: DependencyAnalysis,
    private val varTypeIds: Map<String, Int>,
    private val oracle: EqualityNewOracle
) {
    private val state: MutableMap<String, Root> = mutableMapOf()

    init {
        contextOutline.forEach { (name, outline) ->
            val paramIndex = 0
            val constraints = dependencies.constraints(name)
            var curr = outline
            if (curr !is F) state[name] = Root(outline.convert())
            while (curr is F) {
                TODO()
            }

        }
    }

    /** Must call once for each *parameter* */
    private fun SpecializedSymbolicType.convert(constraint: DependencyConstraint? = null): MutableList<ConstrainedType> =
        when (this) {
            is CL, L -> labels.map { (n, p) -> L(n, MutableList(p) { mutableListOf(Hole()) }, constraint) }
                .toMutableList()
            is F -> mutableListOf(F(this.left.convert(constraint), this.rite.convert(constraint)))
            is N -> throw Exception("shouldn't happen this is bad code quality")
            is VB -> mutableListOf(ConcVB(this.vId, this.tId))
            is VL -> mutableListOf(ConcVL(this.vId, this.tId))
            is VR -> mutableListOf(ConcVR(this.vId, this.tId))
        }

    fun enumerate(): Map<String, ConstrainedType> {

        TODO()
    }

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
