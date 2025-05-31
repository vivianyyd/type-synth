package symbolicgen.concreteenumerator

import symbolicgen.DependencyAnalysis
import symbolicgen.DependencyConstraint
import symbolicgen.std.SymTypeDFlat
import util.EqualityNewOracle
import util.Query

sealed interface Node {
    val constraint: DependencyConstraint?
}

class Hole(override val constraint: DependencyConstraint?) : Node {
    override fun toString(): String = "_"
}

class L(
    val label: Int,
    val params: List<MutableList<Node>>,
    override val constraint: DependencyConstraint?
) : Node {
    constructor(label: Int, numParams: Int, constraint: DependencyConstraint? = null) :
            this(label, (0 until numParams).map { mutableListOf(Hole(constraint)) }, constraint)

    override fun toString(): String = "L$label(${params.joinToString(separator = ",")})"
}

class F(
    val params: List<MutableList<Node>>,
    override val constraint: DependencyConstraint?
) : Node {
    override fun toString(): String = params.joinToString(separator = "->")
}

sealed class Var(open val vid: Int, open val tid: Int, override val constraint: DependencyConstraint?) : Node

data class VB(override val vid: Int, override val tid: Int, override val constraint: DependencyConstraint?) :
    Var(vid, tid, constraint) {
    override fun toString(): String = "${tid}_$vid"
}

data class VR(override val vid: Int, override val tid: Int, override val constraint: DependencyConstraint?) :
    Var(vid, tid, constraint) {
    override fun toString(): String = "${tid}_$vid"
}

data class VL(override val vid: Int, override val tid: Int, override val constraint: DependencyConstraint?) :
    Var(vid, tid, constraint) {
    override fun toString(): String = "${tid}_$vid"
}

class ConcreteEnumerator(
    val query: Query,
    contextOutline: Map<String, SymTypeDFlat>,
    /** Map from label ids to number of parameters */
    private val labels: Map<Int, Int>,
    private val dependencies: DependencyAnalysis,
    private val oracle: EqualityNewOracle
) {
    private val state: MutableMap<String, Node> = mutableMapOf()
    private val variablesInScope: Map<String, MutableList<Pair<Int, Int>>> =
        query.names.associateWith { mutableListOf() }

    private val frontier: MutableList<Node> = mutableListOf()

    init {
        contextOutline.forEach { (name, outline) ->
            val constraints = dependencies.constraints(name)

            fun SymTypeDFlat.toNode(constraint: DependencyConstraint?): Node = when (this) {
                is symbolicgen.std.F ->
                    F(
                        (this.args + this.rite).map { mutableListOf(it.toNode(constraint)) },
                        constraint
                    )
                is symbolicgen.std.L -> {
                    L(this.label, labels[this.label]!!, constraints[0])
                }
                is symbolicgen.std.VB -> VB(this.vId, this.tId, constraint)
                is symbolicgen.std.VL -> VL(this.vId, this.tId, constraint)
                is symbolicgen.std.VR -> VR(this.vId, this.tId, constraint)
            }

            state[name] = when (outline) {
                is symbolicgen.std.F ->
                    F(
                        (outline.args + outline.rite).mapIndexed { i, a -> mutableListOf(a.toNode(constraints[i])) },
                        null
                    )
                is symbolicgen.std.L, is symbolicgen.std.VB, is symbolicgen.std.VL, is symbolicgen.std.VR ->
                    outline.toNode(constraints[0])
            }

            fun variables(outline: SymTypeDFlat): Set<Pair<Int, Int>> = when (outline) {
                is symbolicgen.std.F -> (outline.args.flatMap { variables(it) } + variables(outline.rite)).toSet()
                is symbolicgen.std.L -> setOf()
                is symbolicgen.std.Var -> setOf(outline.vId to outline.tId)
            }
            variablesInScope[name]!!.addAll(variables(outline))
        }
    }

    /** While we start with all functions flattened, we might enumerate functions with functions as outputs */
    private fun filler(name: String, constraint: DependencyConstraint?) =
        labels.map { L(it.key, it.value, constraint) } +
                variablesInScope[name]!!.map { VR(it.first, it.second, constraint) } +
                F(listOf(mutableListOf(Hole(constraint)), mutableListOf(Hole(constraint))), constraint)

    fun callMe(iterations: Int): Map<String, Node> {
        repeat(iterations) { state.forEach { (f, root) -> root.enumerate(f) } }
        return state
    }

    fun Node.enumerate(name: String): Unit = when (this) {
        is Hole -> throw Exception("Should be handled by parent")
        is F -> params.forEach { options ->
            if (options.removeAll { it is Hole }) {
                options.addAll(filler(name, this.constraint))
            } else {
                options.forEach { it.enumerate(name) }
            }
        }
        is L -> params.forEach { options ->
            if (options.removeAll { it is Hole }) {
                options.addAll(filler(name, this.constraint))
            } else {
                options.forEach { it.enumerate(name) }
            }
        }
        is Var -> {}
    }
}
