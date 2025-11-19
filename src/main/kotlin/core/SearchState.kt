package core

import util.Counter
import util.ParameterNode
import java.lang.Integer.max

/** SearchNodes are hashable. All but holes are functional and immutable.
 * Holes mutate when they count conflicts, but they are normal rather than data classes, so they are physical equals */
sealed interface SearchNode<L : Language> {
    fun instantiate(freshIdGen: Counter, instId: Int): ConstraintType<L>

    fun replace(hole: Hole<L>, node: SearchNode<L>): SearchNode<L>

    fun replaceWithAll(hole: Hole<L>, nodes: List<SearchNode<L>>): List<SearchNode<L>>

    fun dfsLeftExpansions(
        unification: Unification<L>,
        vars: Int = 0,
        recursionBound: Int? = null
    ): List<Pair<SearchNode<L>, Commitment<L>>>

    fun dfsPriorityExpansions(
        unification: Unification<L>,
        vars: Int = 0,
        recursionBound: Int? = null
    ): List<Pair<SearchNode<L>, Commitment<L>>>

    /** The priority is the max number of conflicts that some hole in this subtree participates in.
     * TODO: maybe it should be sum instead of max. */
    fun priority(): Int

    /** The total number of nodes, including holes. */
    fun size(): Int

    /** The number of holes. */
    fun holes(): Int

    fun listHoles(): List<Hole<L>>

    /** The number of nodes in the longest path from root to leaf, including holes. */
    fun depth(): Int

    /** TODO not sure if the invariant here should be that num holes = 0 iff full.
     *    I think we need one metric for no more holes *to fill* ,
     *    one metric for it's actually a full type with no holes */
    fun full(): Boolean

    /** The number of parameters this type has. */
    fun params(): Int = when (this) {
        is NArrow -> 1 + r.params()
        else -> 1
    }

    /** Optional for correctness, but helps us recognize alpha equivalences */
    fun variableNames(): Set<Int>

    /** Optional for correctness, but lets us reject bad candidates.
     * While a function certainly return L[a] where a is unbound, it cannot simply return any a. */
    fun noFreshSoleVarOnRHS(): Boolean = when (this) {
        is NArrow -> {
            val vars = this.l.variableNames().toMutableList()
            var rightmost = this.r
            while (rightmost is NArrow) {
                vars.addAll(rightmost.l.variableNames())
                rightmost = rightmost.r
            }
            !((rightmost.variableNames() - vars.toSet()).isNotEmpty() && rightmost is ConcreteV)
        }
        else -> true
    }
}

sealed class Branch<L : Language>(open val params: List<SearchNode<L>>) : SearchNode<L> {
    override fun priority(): Int = params.maxOfOrNull { it.priority() } ?: 0

    override fun size() = size
    private val size by lazy {
        1 + params.sumOf { it.size() }
    }

    override fun holes() = holes
    private val holes by lazy {
        params.sumOf { it.holes() }
    }

    override fun listHoles(): List<Hole<L>> = params.flatMap { it.listHoles() }

    override fun depth() = depth
    private val depth by lazy {
        1 + (params.maxOfOrNull { it.depth() } ?: 0)
    }

    override fun full() = params.all { it.full() }

    override fun variableNames() = params.flatMap { it.variableNames() }.toSet()
}

data class NArrow<L : Language> constructor(
    override val params: List<SearchNode<L>>,
    val contributesToDepth: Boolean
) : Branch<L>(params) {
    val l = params[0]
    val r = params[1]

    constructor(l: SearchNode<L>, r: SearchNode<L>, contributesToDepth: Boolean) : this(
        listOf(l, r),
        contributesToDepth
    )

    override fun depth() = depth
    private val depth by lazy {
        max(l.depth(), r.depth()) + (if (contributesToDepth) 1 else 0)
    }

    override fun toString(): String = "${if (l is NArrow) "($l)" else "$l"} -> $r"

    override fun instantiate(freshIdGen: Counter, instId: Int): ConstraintType<L> =
        CArrow(l.instantiate(freshIdGen, instId), r.instantiate(freshIdGen, instId))

    override fun replace(hole: Hole<L>, node: SearchNode<L>) =
        NArrow(l.replace(hole, node), r.replace(hole, node), contributesToDepth)

    override fun replaceWithAll(hole: Hole<L>, nodes: List<SearchNode<L>>): List<SearchNode<L>> {
        val newL = l.replaceWithAll(hole, nodes)
        val newR = r.replaceWithAll(hole, nodes)
        require(!(newL.size > 1 && newR.size > 1))
        return if (newL.isNotEmpty())
            newL.map { NArrow(it, r, contributesToDepth) }
        else newR.map { NArrow(l, it, contributesToDepth) }
    }

    override fun dfsLeftExpansions(
        unification: Unification<L>,
        vars: Int,
        recursionBound: Int?
    ): List<Pair<SearchNode<L>, Commitment<L>>> {
        val nextBound = recursionBound?.let { it - (if (contributesToDepth) 1 else 0) }
        val left = l.dfsLeftExpansions(unification, vars, nextBound).map { (node, commit) ->
            NArrow(node, r, contributesToDepth) to commit
        }
        val right = if (left.isEmpty() || (left.toSet().size == 1 && left.first().first.l == l))
            r.dfsLeftExpansions(unification, vars, nextBound).map { (node, commit) ->
                NArrow(l, node, contributesToDepth) to commit
            } else listOf()
        return (left + right).toSet().toList()
    }

    override fun dfsPriorityExpansions(
        unification: Unification<L>,
        vars: Int,
        recursionBound: Int?
    ): List<Pair<SearchNode<L>, Commitment<L>>> {
        val nextBound = recursionBound?.let { it - (if (contributesToDepth) 1 else 0) }
        if (l.priority() >= r.priority()) {
            val left = l.dfsPriorityExpansions(unification, vars, nextBound).map { (node, commit) ->
                NArrow(node, r, contributesToDepth) to commit
            }
            val right = if (left.isEmpty() || (left.toSet().size == 1 && left.first().first.l == l))
                r.dfsPriorityExpansions(unification, vars, nextBound).map { (node, commit) ->
                    NArrow(l, node, contributesToDepth) to commit
                } else listOf()
            return (left + right).toSet().toList()
        } else {
            val right = r.dfsPriorityExpansions(unification, vars, nextBound).map { (node, commit) ->
                NArrow(l, node, contributesToDepth) to commit
            }
            val left = if (right.isEmpty() || (right.toSet().size == 1 && right.first().first.l == l))
                l.dfsPriorityExpansions(unification, vars, nextBound).map { (node, commit) ->
                    NArrow(node, r, contributesToDepth) to commit
                } else listOf()
            return (right + left).toSet().toList()
        }
    }
}

sealed interface Leaf<L : Language> : SearchNode<L> {
    override fun listHoles(): List<Hole<L>> = listOf()

    override fun replace(hole: Hole<L>, node: SearchNode<L>): SearchNode<L> = this

    override fun replaceWithAll(hole: Hole<L>, nodes: List<SearchNode<L>>) = listOf(this)

    override fun dfsLeftExpansions(
        unification: Unification<L>,
        vars: Int,
        recursionBound: Int?
    ): List<Pair<SearchNode<L>, Commitment<L>>> =
        listOf(this to null)

    override fun dfsPriorityExpansions(
        unification: Unification<L>,
        vars: Int,
        recursionBound: Int?
    ): List<Pair<SearchNode<L>, Commitment<L>>> =
        listOf(this to null)

    override fun priority() = 0
    override fun size() = 1
    override fun holes() = 0
    override fun depth() = 1
    override fun full() = true
}

sealed class Hole<L : Language> : SearchNode<L> {
    companion object {
        var nextHoleId = 0
    }

    val holeId = nextHoleId++

    override fun listHoles(): List<Hole<L>> = listOf(this)

    override fun replace(hole: Hole<L>, node: SearchNode<L>): SearchNode<L> = if (hole == this) node else this

    override fun replaceWithAll(hole: Hole<L>, nodes: List<SearchNode<L>>) = if (hole == this) nodes else listOf(this)

    abstract fun expansions(
        unification: Unification<L>,
        vars: Int,
        mustBeLeaf: Boolean
    ): List<SearchNode<L>>

    fun expansionsWithCommits(
        unification: Unification<L>,
        vars: Int,
        mustBeLeaf: Boolean
    ): List<Pair<SearchNode<L>, Commitment<L>>> =
        expansions(unification, vars, mustBeLeaf).map { it to (this to it) }

    override fun dfsLeftExpansions(
        unification: Unification<L>,
        vars: Int,
        recursionBound: Int?
    ): List<Pair<SearchNode<L>, Commitment<L>>> =
        expansionsWithCommits(unification, vars, recursionBound != null && recursionBound <= 1)

    override fun dfsPriorityExpansions(
        unification: Unification<L>,
        vars: Int,
        recursionBound: Int?
    ): List<Pair<SearchNode<L>, Commitment<L>>> =
        expansionsWithCommits(unification, vars, recursionBound != null && recursionBound <= 1)

    private val instantiations = mutableListOf<Instantiation<L>>()

    override fun instantiate(freshIdGen: Counter, instId: Int): ConstraintType<L> {
        val inst = Instantiation(this, this.holeId, freshIdGen.get(), instId, freshIdGen)
        instantiations.add(inst)
        return inst
    }

    fun instantiations(): List<Instantiation<L>> = instantiations

    open fun conflict() = conflicts++
    private var conflicts = 0
    override fun priority(): Int = 1 + conflicts
    override fun size() = 1
    override fun holes() = 1
    override fun depth() = 1  // useful for recursion bound
    override fun full() = false
    override fun variableNames() = emptySet<Int>()
    override fun toString() = "_${holeId}_"
}

data class Candidate<L : Language>(val names: List<String>, val types: List<SearchNode<L>>) {
    private var deps: Map<ParameterNode, Dependency>? = null

    constructor(names: List<String>, types: List<SearchNode<L>>, deps: Map<ParameterNode, Dependency>) : this(
        names,
        types
    ) {
        this.deps = deps
    }

    override fun toString(): String = names.zip(types).joinToString(separator = ", ") { "${it.first}: ${it.second}" }

    fun searchNodeOf(name: String): SearchNode<L> = types[names.indexOf(name)]

    val assocList by lazy {
        names.zip(types)
    }

    val size by lazy {
        types.sumOf { it.size() }
    }

    val holes by lazy {
        types.sumOf { it.holes() }
    }

    fun depth() = depth

    private val depth by lazy {
        types.maxOf { it.depth() }
    }

    private fun params(node: NArrow<L>): List<SearchNode<L>> {
        var curr: SearchNode<L> = node
        val p = mutableListOf<SearchNode<L>>()
        while (curr is NArrow<L>) {
            p.add(curr.l)
            curr = curr.r
        }
        p.add(curr)
        return p
    }

    fun params(node: SearchNode<L>) = when (node) {
        is NArrow -> params(node)
        else -> listOf(node)
    }

    fun satisfiesDependencies(): Boolean {
        if (deps == null) return true
        val params = types.map { params(it) }
        return deps!!.all { (param, dep) ->
            val paramNode = params[names.indexOf(param.f)][param.i]
            !paramNode.full() || when (dep) {
                is MustContain -> dep.vars.all { it in paramNode.variableNames() }
                NoVariables -> paramNode.variableNames().isEmpty()
                is Only -> paramNode.variableNames().size == 1 && paramNode.variableNames().first() == dep.v
            }
        }
    }

    val asMap by lazy { names.zip(types).toMap() }

    fun arities() = types.map { it.params() }

    fun full() = types.all { it.full() }

    fun canonical() =
        types.all { it.variableNames().size == (it.variableNames().maxOrNull() ?: -1) + 1 }
    // We can also add it.noFreshSoleVarOnRHS()
}
