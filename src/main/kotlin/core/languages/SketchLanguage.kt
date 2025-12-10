package core.languages

import core.unification.*
import util.Counter

object Sketch : Language

class Blank(
    mayHaveFresh: Boolean,
    constraint: Dependency?,
    labelArities: Map<Int, Int>,
) : SketchHole(mayHaveFresh, constraint, labelArities) {
    override fun conflict() = 0
    override fun priority() = 0
    override fun costToCommit(): Int = 0
    override fun fillable(): List<Hole<Sketch>> = listOf()
    override fun holes() = 1 // TODO not sure about this one
    override fun full() = false // TODO also not sure about this one

    override fun expansions(
        unification: Unification<Sketch>,
        vars: Int,
        mustBeLeaf: Boolean
    ): List<SearchNode<Sketch>> = listOf(this)

    override fun toString() = "☐$holeId"
}

data class SketchV(val v: Int) : Leaf<Sketch> {
    override fun toString() = "V$v"
    override fun instantiate(freshIdGen: Counter, instId: Int): ConstraintType<Sketch> =
        SketchConstrV(v, instId)

    override fun variableNames() = setOf(v)
}

data class SketchL(val id: Int, override val params: List<SearchNode<Sketch>>) :
    Branch<Sketch>(params) {
    override fun toString() = "L$id$params"
    override fun instantiate(freshIdGen: Counter, instId: Int): ConstraintType<Sketch> =
        SketchConstrL.new(id, params.map { it.instantiate(freshIdGen, instId) })

    override fun replace(hole: Hole<Sketch>, node: SearchNode<Sketch>) =
        SketchL(id, params.map { it.replace(hole, node) })

    override fun replaceWithAll(
        hole: Hole<Sketch>,
        nodes: List<SearchNode<Sketch>>
    ): List<SearchNode<Sketch>> {
        val newParams = params.map { it.replaceWithAll(hole, nodes) }
        val changed = newParams.indexOfFirst { it.size > 1 }
        return newParams[changed].map {
            SketchL(id, params.mapIndexed { i, param -> if (i == changed) it else param })
        }
    }

    override fun dfsLeftExpansions(
        unification: Unification<Sketch>, vars: Int, recursionBound: Int?
    ): List<Pair<SearchNode<Sketch>, Commitment<Sketch>>> {
        var cont = true
        return params.indices.flatMap { i ->
            if (cont) {
                val exp =
                    params[i].dfsLeftExpansions(unification, vars, recursionBound?.let { it - 1 })
                        .map { (node, commit) ->
                            SketchL(id, params.mapIndexed { j, p -> if (j == i) node else p }) to commit
                        }
                cont = exp.size <= 1
                exp
            } else listOf()
        } + (if (params.isEmpty()) listOf(this to null) else listOf())
    }

    override fun dfsPriorityExpansions(
        unification: Unification<Sketch>, vars: Int, recursionBound: Int?
    ): List<Pair<SearchNode<Sketch>, Commitment<Sketch>>> {
        var cont = true
        return params.indices.sortedByDescending { params[it].priority() }.flatMap { i ->
            if (cont) {
                val exp =
                    params[i].dfsPriorityExpansions(unification, vars, recursionBound?.let { it - 1 })
                        .map { (node, commit) ->
                            SketchL(id, params.mapIndexed { j, p -> if (j == i) node else p }) to commit
                        }
                cont = exp.size <= 1
                exp
            } else listOf()
        } + (if (params.isEmpty()) listOf(this to null) else listOf())
    }
}

open class SketchHole(
    protected val mayHaveFresh: Boolean,
    protected val constraint: Dependency?,
    protected val labelArities: Map<Int, Int>,
) : Hole<Sketch>() {
//    override fun toString() = "_${holeId}_s"

    override fun expansions(
        unification: Unification<Sketch>,
        vars: Int,
        mustBeLeaf: Boolean
    ): List<SearchNode<Sketch>> =
        if (mustBeLeaf) expansionsNoBound(unification, vars).filter {
            when (it) {
                is SketchL -> it.params.isEmpty()
                is NArrow -> false
                is SketchHole -> true
                is SketchV -> true
                else -> throw Exception("Impossible")
            }
        } else expansionsNoBound(unification, vars)

    private fun hole() = SketchHole(mayHaveFresh, constraint, labelArities)
    private val fnExpansion by lazy { NArrow(hole(), hole(), true) }
    private val labelExpansions by lazy { labelArities.map { SketchL(it.key, List(it.value) { hole() }) } }
    val blankExpansion by lazy { Blank(mayHaveFresh, constraint, labelArities) }
    private fun variableExpansions(vars: Int) = when (constraint) {  // TODO weird that vars need to be sorted
        null, is MustContain -> (0 until (if (mayHaveFresh) vars + 1 else vars)).map { SketchV(it) }
        NoVariables -> listOf()
        is Only -> listOf(SketchV(constraint.v))
    }

    private fun expansionsNoBound(
        unification: Unification<Sketch>,
        vars: Int,
    ): List<SearchNode<Sketch>> {
        val mustBeCompatible = unification.holeEqualsConstructors(this)

        if (mustBeCompatible.isNotEmpty()) {
            if (mustBeCompatible.any { a -> mustBeCompatible.any { b -> !a.match(b) } }) return variableExpansions(vars)
            if (mustBeCompatible.first() is CArrow && mustBeCompatible.all {
                    mustBeCompatible.first().match(it)
                }) return listOf(fnExpansion) + variableExpansions(vars)  // TODO Think about this
            if (mustBeCompatible.first() is SketchConstrL && mustBeCompatible.all {
                    mustBeCompatible.first().match(it)
                }) {
                val label = (mustBeCompatible.first() as SketchConstrL).label
                // TODO look at the todo in concretehole
                return labelExpansions.filter { it.id == label } + variableExpansions(vars)
            }
        }
        return listOf(blankExpansion) + labelExpansions + variableExpansions(vars) + fnExpansion
    }

    /** Returns the first node if top-level constructors all match; null if mismatch or empty. */
    private fun takeFirstIfMatch(constrs: List<CTypeConstructor<Sketch>>): CTypeConstructor<Sketch>? {
        return if (constrs.isEmpty()) null
        else if (constrs.all { a -> constrs.all { b -> a.match(b) } }) {
            // we only care about the top-level constructor, so it suffices to return an arbitrary element
            constrs.first()
        } else null
    }

    private fun antiunify(
        exprs: List<ConstraintType<Sketch>>, unification: Unification<Sketch>, defaultVariable: SketchConstrV?
    ): ConstraintType<Sketch>? {
        if (exprs.isEmpty()) return defaultVariable  // might as well give this a try
        if (exprs.any { it is SketchConstrV }) return defaultVariable

        val insts = exprs.filterIsInstance<Instantiation<Sketch>>()
        val constructors = exprs.filterIsInstance<CTypeConstructor<Sketch>>()

        if (constructors.isEmpty() || constructors.any { a -> constructors.any { b -> !a.match(b) } })
            return defaultVariable

        /** insts might point to more insts; follow all pointers and collect them.
         * no need til fixpt, just keep separate unseen set and only add those' ptrs
         * TABLED for now, since I think this is a waste of time when all we want is an approximation */
        fun followInstPointers(
            acc: List<Instantiation<Sketch>>, new: List<Instantiation<Sketch>>
        ): List<Instantiation<Sketch>> = TODO()

        // We know they match now
        val auConstrs = when (constructors.first()) {
            is CArrow -> {
                antiunify(constructors.map { (it as CArrow).l }, unification, defaultVariable)?.let { l ->
                    antiunify(constructors.map { (it as CArrow).r }, unification, defaultVariable)?.let { r ->
                        CArrow(l, r)
                    }
                }
            }
            is SketchConstrL -> {
                val params = List(constructors.first().params.size) { i ->
                    antiunify(constructors.map { (it as SketchConstrL).params[i] }, unification, defaultVariable)
                }.filterNotNull()
                if (params.size != constructors.first().params.size) null
                else SketchConstrL(
                    (constructors.first() as SketchConstrL).label,
                    params
                )
            }
            else -> error("Unreachable pattern match")
        }

        return if (auConstrs != null) {
            val instsPointTo = insts.mapNotNull {
                val instEqs = unification.holeEquals(it.holeId)
                // Ignore the other insts if unconstrained, if it can be a variable, or constructors mismatch
                if (instEqs.any { it is SketchConstrV }) null
                else takeFirstIfMatch(instEqs.filterIsInstance<CTypeConstructor<Sketch>>())
            }
            takeFirstIfMatch(listOf(auConstrs) + instsPointTo)
        } else null
    }

    private fun ConstraintType<Sketch>.toNode(): SearchNode<Sketch> = when (this) {
        is CArrow -> NArrow(
            this.l.toNode(),
            this.r.toNode(),
            contributesToDepth = false
        ) // depth arg not quite right here, but good enough
        is SketchConstrL -> SketchL(this.label, this.params.map { it.toNode() })
        is SketchConstrV -> SketchV(this.v)
        is Instantiation -> error("Unreachable pattern match - convert Instantiation to node")
        is ProofVariable -> error("Unreachable pattern match - convert ProofVariable to node")
        else -> error("Unreachable pattern match")
    }

    override fun fastForward(unification: Unification<Sketch>, vars: Int): SearchNode<Sketch>? {
        val vExp = variableExpansions(vars)
        val defaultVariable =
            if (vExp.isNotEmpty()) SketchConstrV(vExp.first().v, instId = 0)  // instId shouldn't matter, dummy here
//        if (constraint is Only) SketchConstrV(constraint.v, instId = 0)
            else null  // Not sure if we want this

        val antiunifies = unification.holeEquals(this)
            .filter { it !is ProofVariable }  // let's ignore proof variables TODO this can be cleaned up but I don't wanna deal with it rn

//        println("Hole: $this\nAntiunifies: $antiunifies")

        val tmp = antiunify(antiunifies, unification, defaultVariable)?.toNode()
//        println("Result: $tmp")
        return tmp
    }
}
