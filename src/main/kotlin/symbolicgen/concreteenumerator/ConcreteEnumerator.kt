package symbolicgen.concreteenumerator

import symbolicgen.DependencyAnalysis
import symbolicgen.DependencyConstraint
import symbolicgen.symbolicenumerator.EnumeratedSymbolicType
import symbolicgen.symbolicenumerator.VB
import symbolicgen.symbolicenumerator.VL
import symbolicgen.symbolicenumerator.VR
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

class F(val left: MutableList<ConstrainedType>, val rite: MutableList<ConstrainedType>) : ConstrainedType
data class ConcVB(val vid: Int, val tid: Int) : ConcreteType
data class ConcVR(val vid: Int, val tid: Int) : ConcreteType
data class ConcVL(val vid: Int, val tid: Int) : ConcreteType

class ConcreteEnumerator(
    val query: Query,
    private val contextOutline: Map<String, EnumeratedSymbolicType>,
    private val dependencies: DependencyAnalysis,
    private val varTypeIds: Map<String, Int>,
    private val oracle: EqualityNewOracle
) {
    private val state: MutableMap<String, Root> = mutableMapOf()

    init {
        contextOutline.forEach { (name, outline) ->

            // TODO flatten outlines into fns with mulitple arguments
            val paramIndex = 0
            val constraints = dependencies.constraints(name)
            var curr = outline
            if (curr !is F) state[name] = Root(outline.convert(constraints))
            while (curr is F) {
                TODO()
            }

        }
    }

    /** Must call once for each *parameter* */
    private fun EnumeratedSymbolicType.convert(constraint: DependencyConstraint? = null): MutableList<ConstrainedType> =
        when (this) {
//            is CL, L -> labels.map { (n, p) -> L(n, MutableList(p) { mutableListOf(Hole()) }, constraint) }
//                .toMutableList()
//            is F -> mutableListOf(F(this.left.convert(constraint), this.rite.convert(constraint)))
//            is N -> throw Exception("shouldn't happen this is bad code quality")
//            is VB -> mutableListOf(ConcVB(this.vId, this.tId))
//            is VL -> mutableListOf(ConcVL(this.vId, this.tId))
//            is VR -> mutableListOf(ConcVR(this.vId, this.tId))
            is F -> TODO()
            is L -> TODO()
            is VB -> TODO()
            is VL -> TODO()
            is VR -> TODO()
        }

    fun enumerate(): Map<String, ConstrainedType> {

        TODO()
    }
}
