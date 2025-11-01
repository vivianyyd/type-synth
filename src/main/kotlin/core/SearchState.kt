package core

import util.Counter
import util.lazyCartesianProduct
import java.lang.Integer.max

/** SearchNodes are functional and immutable... except for Holes. So they are not
 * Only full types are hashable */
sealed interface SearchNode<L : Language> {
    fun instantiate(freshIdGen: Counter, instId: Int): ConstraintType<L>
    fun bfsExpansions(
        constrs: List<Constraint<L>> = listOf(),
        vars: Set<Int> = setOf(),  // TODO if we do this correctly, this can just be an int
        recursionBound: Int? = null
    ): List<Pair<SearchNode<L>, Commitment<L>>>

    fun dfsLeftExpansions(
        constrs: List<Constraint<L>> = listOf(),
        vars: Set<Int> = setOf(),  // TODO if we do this correctly, this can just be an int
        recursionBound: Int? = null
    ): List<Pair<SearchNode<L>, Commitment<L>>>

    fun dfsPriorityExpansions(
        constrs: List<Constraint<L>> = listOf(),
        vars: Set<Int> = setOf(),  // TODO if we do this correctly, this can just be an int
        recursionBound: Int? = null
    ): List<Pair<SearchNode<L>, Commitment<L>>>

    fun priority(): Int
    fun size(): Int
    fun holes(): Int
    fun depth(): Int
    fun full(): Boolean

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

    override fun depth() = depth
    private val depth by lazy {
        1 + (params.maxOfOrNull { it.depth() } ?: 0)
    }

    override fun full() = params.all { it.full() }

    override fun variableNames() = params.flatMap { it.variableNames() }.toSet()
}

data class NArrow<L : Language> private constructor(
    override val params: List<SearchNode<L>>,
    private val contributesToDepth: Boolean
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

    override fun bfsExpansions(
        constrs: List<Constraint<L>>,
        vars: Set<Int>,
        recursionBound: Int?
    ): List<Pair<SearchNode<L>, Commitment<L>>> {
        // If we use prod, hole expansion cannot include itself, or blowup is too fast...
        // multiple commitments made at once if we use prod
//         val prod = lazyCartesianProduct(listOf(params[0].expansions(), params[1].expansions())).map {
//             NArrow(it)
//         }
        val nextBound = recursionBound?.let { it - (if (contributesToDepth) 1 else 0) }
        val one = (l.bfsExpansions(constrs, vars, nextBound).map { (node, commit) ->
            NArrow(node, r, contributesToDepth) to commit
        } + r.bfsExpansions(constrs, vars, nextBound).map { (node, commit) ->
            NArrow(l, node, contributesToDepth) to commit
        })
        return one.toSet().toList()
    }

    override fun dfsLeftExpansions(
        constrs: List<Constraint<L>>,
        vars: Set<Int>,
        recursionBound: Int?
    ): List<Pair<SearchNode<L>, Commitment<L>>> {
        val nextBound = recursionBound?.let { it - (if (contributesToDepth) 1 else 0) }
        val left = l.dfsLeftExpansions(constrs, vars, nextBound).map { (node, commit) ->
            NArrow(node, r, contributesToDepth) to commit
        }
        val right = if (left.isEmpty() || (left.toSet().size == 1 && left.first().first.l == l))
            r.dfsLeftExpansions(constrs, vars, nextBound).map { (node, commit) ->
                NArrow(l, node, contributesToDepth) to commit
            } else listOf()
        return (left + right).toSet().toList()
    }

    override fun dfsPriorityExpansions(
        constrs: List<Constraint<L>>,
        vars: Set<Int>,
        recursionBound: Int?
    ): List<Pair<SearchNode<L>, Commitment<L>>> {
        val nextBound = recursionBound?.let { it - (if (contributesToDepth) 1 else 0) }
        if (l.priority() == r.priority()) return dfsLeftExpansions(constrs, vars, recursionBound)
        if (l.priority() > r.priority()) {
            val left = l.dfsPriorityExpansions(constrs, vars, nextBound).map { (node, commit) ->
                NArrow(node, r, contributesToDepth) to commit
            }
            val right = if (left.isEmpty() || (left.toSet().size == 1 && left.first().first.l == l))
                r.dfsLeftExpansions(constrs, vars, nextBound).map { (node, commit) ->
                    NArrow(l, node, contributesToDepth) to commit
                } else listOf()
            return (left + right).toSet().toList()
        } else {
            val right = r.dfsLeftExpansions(constrs, vars, nextBound).map { (node, commit) ->
                NArrow(l, node, contributesToDepth) to commit
            }
            val left = if (right.isEmpty() || (right.toSet().size == 1 && right.first().first.l == l))
                l.dfsPriorityExpansions(constrs, vars, nextBound).map { (node, commit) ->
                    NArrow(node, r, contributesToDepth) to commit
                } else listOf()
            return (right + left).toSet().toList()
        }
    }
}

sealed interface Leaf<L : Language> : SearchNode<L> {
    override fun bfsExpansions(
        constrs: List<Constraint<L>>,
        vars: Set<Int>,
        recursionBound: Int?
    ): List<Pair<SearchNode<L>, Commitment<L>>> =
        listOf(this to null)

    override fun dfsLeftExpansions(
        constrs: List<Constraint<L>>,
        vars: Set<Int>,
        recursionBound: Int?
    ): List<Pair<SearchNode<L>, Commitment<L>>> =
        listOf(this to null)

    override fun dfsPriorityExpansions(
        constrs: List<Constraint<L>>,
        vars: Set<Int>,
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

    abstract fun expansions(
        constrs: List<Constraint<L>>,
        vars: Set<Int>,
        recursionBound: Int?
    ): List<Pair<SearchNode<L>, Commitment<L>>>

    override fun bfsExpansions(
        constrs: List<Constraint<L>>,
        vars: Set<Int>,
        recursionBound: Int?
    ): List<Pair<SearchNode<L>, Commitment<L>>> = expansions(constrs, vars, recursionBound)

    override fun dfsLeftExpansions(
        constrs: List<Constraint<L>>,
        vars: Set<Int>,
        recursionBound: Int?
    ): List<Pair<SearchNode<L>, Commitment<L>>> = expansions(constrs, vars, recursionBound)

    override fun dfsPriorityExpansions(
        constrs: List<Constraint<L>>,
        vars: Set<Int>,
        recursionBound: Int?
    ): List<Pair<SearchNode<L>, Commitment<L>>> = expansions(constrs, vars, recursionBound)

    private val instantiations = mutableListOf<Instantiation<L>>()

    override fun instantiate(freshIdGen: Counter, instId: Int): ConstraintType<L> {
        val inst = Instantiation(this, this.holeId, freshIdGen.get(), instId, freshIdGen)
        instantiations.add(inst)
        return inst
    }

    fun instantiations(): List<Instantiation<L>> = instantiations

    fun conflict() = conflicts++
    private var conflicts = 0
    override fun priority(): Int = 1 + conflicts
    override fun size() = 1
    override fun holes() = 1
    override fun depth() = 1  // TODO think about me
    override fun full() = false
    override fun variableNames() = emptySet<Int>()
    override fun toString() = "_${holeId}_"
}

data class Candidate<L : Language>(val names: List<String>, val types: List<SearchNode<L>>) {
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

    fun asMap() = names.zip(types).toMap()

    fun arities() = types.map { it.params() }

    fun full() = types.all { it.full() }

    fun canonical() = types.all { it.variableNames().size == (it.variableNames().maxOrNull() ?: -1) + 1 }
    // We can also add it.noFreshSoleVarOnRHS()

    fun bfsExpansions(constrs: List<Constraint<L>> = listOf()): Sequence<Candidate<L>> {
        // TODO should this be product, or also one at a time?? either will work but what is better
        return lazyCartesianProduct(types.map {
            // TODO we don't really learn from bad combinations here
            // Each expansion corresponds with concretizing one hole. We check constrs after refining corresponding inst
            // variables, this lets us check w inherited constrs from parent. If we can elim many this way, we save a
            // lot of space from not keeping around bad candidates in frontier only to find they are bad later.
            // We also use one construction of constraints to prune many expansions
            it.bfsExpansions(constrs, it.variableNames())
        }).mapNotNull {

            val (types, commitments) = it.unzip()

            // Micro-opt: If the commitment refines a hole to a fresh variable, no need to check validity
            if (it.all { (ty, commit) ->
                    commit == null ||
                            (commit.second is ConcreteV && (commit.second as ConcreteV).v !in ty.variableNames() && TODO(
                                "This is wrong - we check the new ty's variableNames, so the second branch will always be false!"
                            ))
                })
                Candidate(names, types)

            if (Unification(constrs).commitAndCheckValid(commitments.filterNotNull())) Candidate(names, types)
            else null  // Could count here for eval
//            Candidate(names, types)  // Originally
        }
    }
}
