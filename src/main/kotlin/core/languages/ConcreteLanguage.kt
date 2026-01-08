package core.languages

import core.unification.*
import util.Counter

object Concrete : Language

class Blank(
    mayHaveFresh: Boolean,
    constraint: Dependency?,
    labelArities: Map<Int, Int>,
    emitBlanks: Boolean
) : ConcreteHole(mayHaveFresh, constraint, labelArities, emitBlanks) {
    override fun conflict() = 0

    override fun priority() = 0

    override fun costToCommit(): Int = 0

    override fun fillable(): List<Hole<Concrete>> = listOf()

    override fun holes() = 1 // TODO not sure about this one

    override fun full() = false // TODO also not sure about this one

    override fun expansions(
        unification: Unification<Concrete>,
        vars: Int,
        mustBeLeaf: Boolean
    ): List<SearchNode<Concrete>> = listOf(this)

    override fun toString() = "☐$holeId"
}

data class ConcreteV(val v: Int) : Leaf<Concrete> {
    override fun toString() = "V$v"

    override fun instantiate(freshIdGen: Counter, instId: Int): ConstraintType<Concrete> =
        ConcreteConstrV(v, instId)

    override fun variableNames() = setOf(v)
}

data class ConcreteL(val id: Int, override val params: List<SearchNode<Concrete>>) :
    Branch<Concrete>(params) {
    override fun toString() = "L$id$params"

    override fun instantiate(freshIdGen: Counter, instId: Int): ConstraintType<Concrete> =
        ConcreteConstrL.new(id, params.map { it.instantiate(freshIdGen, instId) })

    override fun replace(hole: Hole<Concrete>, node: SearchNode<Concrete>) =
        ConcreteL(id, params.map { it.replace(hole, node) })

    override fun replaceWithAll(
        hole: Hole<Concrete>,
        nodes: List<SearchNode<Concrete>>
    ): List<SearchNode<Concrete>> {
        val newParams = params.map { it.replaceWithAll(hole, nodes) }
        val changed = newParams.indexOfFirst { it.size > 1 }
        return newParams[changed].map {
            ConcreteL(id, params.mapIndexed { i, param -> if (i == changed) it else param })
        }
    }

    override fun dfsLeftExpansions(
        unification: Unification<Concrete>,
        vars: Int,
        recursionBound: Int?
    ): List<Pair<SearchNode<Concrete>, Commitment<Concrete>>> {
        var cont = true
        return params.indices.flatMap { i ->
            if (cont) {
                val exp =
                    params[i]
                        .dfsLeftExpansions(unification, vars, recursionBound?.let { it - 1 })
                        .map { (node, commit) ->
                            ConcreteL(id, params.mapIndexed { j, p -> if (j == i) node else p }) to
                                commit
                        }
                cont = exp.size <= 1
                exp
            } else listOf()
        } + (if (params.isEmpty()) listOf(this to null) else listOf())
    }

    override fun dfsPriorityExpansions(
        unification: Unification<Concrete>,
        vars: Int,
        recursionBound: Int?
    ): List<Pair<SearchNode<Concrete>, Commitment<Concrete>>> {
        var cont = true
        return params.indices
            .sortedByDescending { params[it].priority() }
            .flatMap { i ->
                if (cont) {
                    val exp =
                        params[i]
                            .dfsPriorityExpansions(
                                unification, vars, recursionBound?.let { it - 1 })
                            .map { (node, commit) ->
                                ConcreteL(
                                    id, params.mapIndexed { j, p -> if (j == i) node else p }) to
                                    commit
                            }
                    cont = exp.size <= 1
                    exp
                } else listOf()
            } + (if (params.isEmpty()) listOf(this to null) else listOf())
    }
}

open class ConcreteHole(
    protected val mayHaveFresh: Boolean,
    protected val constraint: Dependency?,
    protected val labelArities: Map<Int, Int>,
    protected val emitBlanks: Boolean
) : Hole<Concrete>() {
    override fun expansions(
        unification: Unification<Concrete>,
        vars: Int,
        mustBeLeaf: Boolean
    ): List<SearchNode<Concrete>> =
        if (mustBeLeaf)
            expansionsNoBound(unification, vars).filter {
                when (it) {
                    is ConcreteL -> it.params.isEmpty()
                    is NArrow -> false
                    is ConcreteHole -> true
                    is ConcreteV -> true
                    else -> throw Exception("Impossible")
                }
            }
        else expansionsNoBound(unification, vars)

    private fun hole() = ConcreteHole(mayHaveFresh, constraint, labelArities, emitBlanks)

    private val fnExpansion by lazy { NArrow(hole(), hole(), true) }
    private val labelExpansions by lazy {
        labelArities.map { ConcreteL(it.key, List(it.value) { hole() }) }
    }
    val blankExpansion by lazy { Blank(mayHaveFresh, constraint, labelArities, emitBlanks) }

    private fun variableExpansions(vars: Int) =
        when (constraint) { // TODO weird that vars need to be sorted
            null,
            is MustContain -> (0 until (if (mayHaveFresh) vars + 1 else vars)).map { ConcreteV(it) }
            NoVariables -> listOf()
            is Only -> listOf(ConcreteV(constraint.v))
        }

    private fun expansionsNoBound(
        unification: Unification<Concrete>,
        vars: Int,
    ): List<SearchNode<Concrete>> {
        val mustBeCompatible = unification.holeEqualsConstructors(this)

        if (mustBeCompatible.isNotEmpty()) {
            if (mustBeCompatible.any { a -> mustBeCompatible.any { b -> !a.match(b) } })
                return variableExpansions(vars)
            if (mustBeCompatible.first() is CArrow &&
                mustBeCompatible.all { mustBeCompatible.first().match(it) }
            )
                return listOf(fnExpansion) + variableExpansions(vars) // TODO Think about this
            if (mustBeCompatible.first() is ConcreteConstrL &&
                mustBeCompatible.all { mustBeCompatible.first().match(it) }
            ) {
                val label = (mustBeCompatible.first() as ConcreteConstrL).label
                // TODO labelExpansions should be an array or something
                return labelExpansions.filter { it.id == label } + variableExpansions(vars)
            }
        }
        return labelExpansions + // (if (emitBlanks) listOf(blankExpansion) else listOf()) +
                variableExpansions(vars) +
                fnExpansion
    }

    /** Returns the first node if top-level constructors all match; null if mismatch or empty. */
    private fun takeFirstIfMatch(
        constrs: List<CTypeConstructor<Concrete>>
    ): CTypeConstructor<Concrete>? {
        return if (constrs.isEmpty()) null
        else if (constrs.all { a -> constrs.all { b -> a.match(b) } }) {
            // we only care about the top-level constructor, so it suffices to return an arbitrary
            // element
            constrs.first()
        } else null
    }

    private fun antiunify(
        exprs: List<ConstraintType<Concrete>>,
        unification: Unification<Concrete>,
        defaultVariable: ConcreteConstrV?
    ): ConstraintType<Concrete>? {
        if (exprs.isEmpty()) return defaultVariable // might as well give this a try
        if (exprs.any { it is ConcreteConstrV }) return defaultVariable

        val insts = exprs.filterIsInstance<Instantiation<Concrete>>()
        val constructors = exprs.filterIsInstance<CTypeConstructor<Concrete>>()

        if (constructors.isEmpty() ||
            constructors.any { a -> constructors.any { b -> !a.match(b) } }
        )
            return defaultVariable

        // We know they match now
        val auConstrs =
            when (constructors.first()) {
                is CArrow -> {
                    antiunify(constructors.map { (it as CArrow).l }, unification, defaultVariable)
                        ?.let { l ->
                            antiunify(
                                constructors.map { (it as CArrow).r },
                                unification,
                                defaultVariable
                            )
                                ?.let { r -> CArrow(l, r) }
                        }
                }
                is ConcreteConstrL -> {
                    val params =
                        List(constructors.first().params.size) { i ->
                            antiunify(
                                constructors.map { (it as ConcreteConstrL).params[i] },
                                unification,
                                defaultVariable
                            )
                        }
                            .filterNotNull()
                    if (params.size != constructors.first().params.size) null
                    else ConcreteConstrL((constructors.first() as ConcreteConstrL).label, params)
                }
                else -> error("Unreachable pattern match")
            }

        return if (auConstrs != null) {
            val instsPointTo =
                insts.mapNotNull {
                    val instEqs = unification.holeEquals(it.holeId)
                    // Ignore the other insts if unconstrained, if it can be a variable, or
                    // constructors mismatch
                    if (instEqs.any { it is ConcreteConstrV }) null
                    else takeFirstIfMatch(instEqs.filterIsInstance<CTypeConstructor<Concrete>>())
                }
            takeFirstIfMatch(listOf(auConstrs) + instsPointTo)
        } else null
    }

    private fun ConstraintType<Concrete>.toNode(): SearchNode<Concrete> =
        when (this) {
            is CArrow ->
                NArrow(
                    this.l.toNode(),
                    this.r.toNode(),
                    contributesToDepth = false
                ) // depth arg not quite right here, but good enough
            is ConcreteConstrL -> ConcreteL(this.label, this.params.map { it.toNode() })
            is ConcreteConstrV -> ConcreteV(this.v)
            is Instantiation -> error("Unreachable pattern match - convert Instantiation to node")
            else -> error("Unreachable pattern match")
        }

    override fun fastForward(unification: Unification<Concrete>, vars: Int): SearchNode<Concrete>? {
        val vExp = variableExpansions(vars)
        val defaultVariable =
            if (vExp.isNotEmpty())
                ConcreteConstrV(vExp.first().v, instId = 0) // instId shouldn't matter, dummy here
            else null

        val antiunifies = unification.holeEquals(this)
        return antiunify(antiunifies, unification, defaultVariable)?.toNode()
    }
}
