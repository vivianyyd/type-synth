package core.languages

import core.unification.*
import util.Counter

object Concrete : Language

/** ConcreteNode interface - helps maintain what variables have already been chosen in the type.
 * We need a way to check alpha equivalence
 * helper function for expansions()?
 * Each node stores numVars in the type it's in. This shouldn't affect equals since types equal implies num vars equal.
 * */

data class ConcreteV(val v: Int) : Leaf<Concrete> {
    override fun toString() = "V$v"
    override fun instantiate(freshIdGen: Counter, instId: Int): ConstraintType<Concrete> = ConcreteConstrV(v, instId)
    override fun variableNames() = setOf(v)
}

data class ConcreteL(val id: Int, override val params: List<SearchNode<Concrete>>) :
    Branch<Concrete>(params) {
    override fun toString() = "L$id$params"
    override fun instantiate(freshIdGen: Counter, instId: Int): ConstraintType<Concrete> =
        ConcreteConstrL.new(id, params.map { it.instantiate(freshIdGen, instId) })

    override fun replace(hole: Hole<Concrete>, node: SearchNode<Concrete>) =
        ConcreteL(id, params.map { it.replace(hole, node) })

    override fun replaceWithAll(hole: Hole<Concrete>, nodes: List<SearchNode<Concrete>>): List<SearchNode<Concrete>> {
        val newParams = params.map { it.replaceWithAll(hole, nodes) }
        val changed = newParams.indexOfFirst { it.size > 1 }
        return newParams[changed].map {
            ConcreteL(id, params.mapIndexed { i, param -> if (i == changed) it else param })
        }
    }

    override fun dfsLeftExpansions(
        unification: Unification<Concrete>, vars: Int, recursionBound: Int?
    ): List<Pair<SearchNode<Concrete>, Commitment<Concrete>>> {
        var cont = true
        return params.indices.flatMap { i ->
            if (cont) {
                val exp =
                    params[i].dfsLeftExpansions(unification, vars, recursionBound?.let { it - 1 })
                        .map { (node, commit) ->
                            ConcreteL(id, params.mapIndexed { j, p -> if (j == i) node else p }) to commit
                        }
                cont = exp.size <= 1
                exp
            } else listOf()
        } + (if (params.isEmpty()) listOf(this to null) else listOf())
    }

    override fun dfsPriorityExpansions(
        unification: Unification<Concrete>, vars: Int, recursionBound: Int?
    ): List<Pair<SearchNode<Concrete>, Commitment<Concrete>>> {
        var cont = true
        return params.indices.sortedByDescending { params[it].priority() }.flatMap { i ->
            if (cont) {
                val exp =
                    params[i].dfsPriorityExpansions(unification, vars, recursionBound?.let { it - 1 })
                        .map { (node, commit) ->
                            ConcreteL(id, params.mapIndexed { j, p -> if (j == i) node else p }) to commit
                        }
                cont = exp.size <= 1
                exp
            } else listOf()
        } + (if (params.isEmpty()) listOf(this to null) else listOf())
    }
}

class ConcreteHole(
    private val mayHaveFresh: Boolean,
    private val constraint: Dependency?,
    private val labelArities: Map<Int, Int>,
) : Hole<Concrete>() {
    override fun expansions(
        unification: Unification<Concrete>,
        vars: Int,
        mustBeLeaf: Boolean
    ): List<SearchNode<Concrete>> =
        if (mustBeLeaf) expansionsNoBound(unification, vars).filter {
            when (it) {
                is ConcreteL -> it.params.isEmpty()
                is NArrow -> false
                is ConcreteHole -> true
                is ConcreteV -> true
                else -> throw Exception("Impossible")
            }
        } else expansionsNoBound(unification, vars)

    private fun hole() = ConcreteHole(mayHaveFresh, constraint, labelArities)
    private val fnExpansion by lazy { NArrow(hole(), hole(), true) }
    private val labelExpansions by lazy { labelArities.map { ConcreteL(it.key, List(it.value) { hole() }) } }
    private fun variableExpansions(vars: Int) = when (constraint) {  // TODO weird that vars need to be sorted
        null, is MustContain -> (0 until (if (mayHaveFresh) vars + 1 else vars)).map { ConcreteV(it) }
        NoVariables -> listOf()
        is Only -> listOf(ConcreteV(constraint.v))
    }

    private fun expansionsNoBound(
        unification: Unification<Concrete>,
        vars: Int,
    ): List<SearchNode<Concrete>> {
        val mustBeCompatible = unification.holeEqualsConstructors(this)

        if (mustBeCompatible.isNotEmpty()) {
            if (mustBeCompatible.any { a -> mustBeCompatible.any { b -> !a.match(b) } }) return variableExpansions(vars)
            if (mustBeCompatible.first() is CArrow && mustBeCompatible.all {
                    mustBeCompatible.first().match(it)
                }) return listOf(fnExpansion) + variableExpansions(vars)  // TODO Think about this
            if (mustBeCompatible.first() is ConcreteConstrL && mustBeCompatible.all {
                    mustBeCompatible.first().match(it)
                }) {
                val label = (mustBeCompatible.first() as ConcreteConstrL).label
                // TODO labelExpansions should be an array or something
                return labelExpansions.filter { it.id == label } + variableExpansions(vars)
            }
            // TODO can't do this for labels bc sometimes we have less constraints bc of lack of earlier commitments.
            //   we might erroneously commit to list of int bc we haven't yet committed to a different thing being list of bool.
            //   AH, but, *if* there is only one label here, the only label expansion we could have is that label!
            //       and we can say this recursively too
        }

        // TODO hilariously, I think the order makes a difference here. we should sort by size tbh
        return labelExpansions + variableExpansions(vars) + fnExpansion
    }

    /** Returns the first node if top-level constructors all match; null if mismatch or empty. */
    private fun takeFirstIfMatch(constrs: List<CTypeConstructor<Concrete>>): CTypeConstructor<Concrete>? {
        return if (constrs.isEmpty()) null
        else if (constrs.all { a -> constrs.all { b -> a.match(b) } }) {
            // we only care about the top-level constructor, so it suffices to return an arbitrary element
            constrs.first()
        } else null
    }

    private fun antiunify(
        exprs: List<ConstraintType<Concrete>>, unification: Unification<Concrete>, defaultVariable: ConcreteConstrV?
    ): ConstraintType<Concrete>? {
        if (exprs.isEmpty()) return defaultVariable  // might as well give this a try
        if (exprs.any { it is ConcreteConstrV }) return defaultVariable

        val insts = exprs.filterIsInstance<Instantiation<Concrete>>()
        val constructors = exprs.filterIsInstance<CTypeConstructor<Concrete>>()

        /** insts might point to more insts; follow all pointers and collect them.
         * no need til fixpt, just keep separate unseen set and only add those' ptrs
         * TABLED for now, since I think this is a waste of time when all we want is an approximation */
        fun followInstPointers(
            acc: List<Instantiation<Concrete>>, new: List<Instantiation<Concrete>>
        ): List<Instantiation<Concrete>> = TODO()

        val instsPointTo = insts.mapNotNull {
            val instEqs = unification.holeEquals(it.holeId)
            // Ignore the other insts if unconstrained, if it can be a variable, or constructors mismatch
            if (instEqs.any { it is ConcreteConstrV }) null
            else takeFirstIfMatch(instEqs.filterIsInstance<CTypeConstructor<Concrete>>())
        }

        if (constructors.isEmpty() || constructors.any { a -> constructors.any { b -> !a.match(b) } })
            return defaultVariable

        // We know they match now
        val auConstrs = when (constructors.first()) {
            is CArrow -> {
                antiunify(constructors.map { (it as CArrow).l }, unification, defaultVariable)?.let { l ->
                    antiunify(constructors.map { (it as CArrow).r }, unification, defaultVariable)?.let { r ->
                        CArrow(l, r)
                    }
                }
            }
            is ConcreteConstrL -> {
                val params = List(constructors.first().params.size) { i ->
                    antiunify(constructors.map { (it as ConcreteConstrL).params[i] }, unification, defaultVariable)
                }.filterNotNull()
                if (params.size != constructors.first().params.size) null
                else ConcreteConstrL(
                    (constructors.first() as ConcreteConstrL).label,
                    params
                )
            }
            else -> error("Unreachable pattern match")
        }

        return if (auConstrs != null) takeFirstIfMatch(listOf(auConstrs) + instsPointTo) else null
    }

    fun ConstraintType<Concrete>.toNode(): SearchNode<Concrete> = when (this) {
        is CArrow -> NArrow(
            this.l.toNode(),
            this.r.toNode(),
            contributesToDepth = false
        ) // depth arg not quite right here, but good enough
        is ConcreteConstrL -> ConcreteL(this.label, this.params.map { it.toNode() })
        is ConcreteConstrV -> ConcreteV(this.v)
        is Instantiation -> error("Unreachable pattern match - convert Instantiation to node")
        is ProofVariable -> error("Unreachable pattern match - convert ProofVariable to node")
        else -> error("Unreachable pattern match")
    }

    override fun fastForward(unification: Unification<Concrete>, vars: Int): SearchNode<Concrete>? {
        val vExp = variableExpansions(vars)
        val defaultVariable =
            if (vExp.isNotEmpty()) ConcreteConstrV(vExp.first().v, instId = 0)  // instId shouldn't matter, dummy here
            else null  // Not sure if we want this

        val antiunifies = unification.holeEquals(this)
            .filter { it !is ProofVariable }  // let's ignore proof variables TODO this can be cleaned up but I don't wanna deal with it rn
        return antiunify(antiunifies, unification, defaultVariable)?.toNode()
    }
}
