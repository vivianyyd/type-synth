package core

import dependencyanalysis.DependencyAnalysis
import query.Name
import query.Query
import stc.Var
import util.*

/** Defines locations of type constructors vs variables and function arities */
object Init : Language

object InitV : Leaf<Init> {
    override fun toString() = "V"
    override fun instantiate(freshIdGen: Counter, instId: Int): ConstraintType<Init> = InitConstrV
    override fun variableNames() = emptySet<Int>()
}

object InitL : Leaf<Init> {
    override fun toString() = "L"
    override fun instantiate(freshIdGen: Counter, instId: Int): ConstraintType<Init> = InitConstrL
    override fun variableNames() = emptySet<Int>()
}

class InitHole : Hole<Init>() {
    /** val so we can prioritize holes correctly, but must be lazy, we only use it when expanding, otherwise stackoverflow lol */
    val fnExpansion by lazy { NArrow(InitHole(), InitHole(), true) }

    override fun expansions(
        unification: Unification<Init>,
        vars: Int,
        recursionBound: Int?
    ): List<Pair<SearchNode<Init>, Commitment<Init>>> {
        val mustBeCompatible = unification.holeEquals(this)
        val fn = if (recursionBound != null && recursionBound <= 1) listOf()
        else if (mustBeCompatible.any { it is CArrow }) listOf(fnExpansion) else listOf()
        return (listOf(InitV, InitL) + fn).map { it to (this to it) }
    }
}

object InitConstrV : CVariable<Init>() {
    override fun toString() = "V"
}

object InitConstrL : CTypeConstructor<Init>(mutableListOf()) {
    override fun match(other: CTypeConstructor<Init>): Boolean = other is InitConstrL
    override fun toString() = "L"
}

fun compileInit(seed: Candidate<Init>): Candidate<Elab> {
    fun compile(seed: SearchNode<Init>): SearchNode<Elab> = when (seed) {
        is NArrow -> {
            val leftTy = compile(seed.l)
            val rightTy = compile(seed.r)
            NArrow(leftTy, rightTy, true)
        }
        InitL -> ElabL
        InitV -> ElabVarHole()
        is InitHole -> throw Exception("Invariant broken")
        else -> throw Exception("Will never happen due to types")
    }
    return Candidate(seed.names, seed.types.map { compile(it) })
}

object Elab : Language

// TODO: Add to canonical: output shouldn't be an unbound variable. Vars should go in increasing order

data class ElabV(val v: Int) : Leaf<Elab> {
    override fun toString() = "V$v"
    override fun instantiate(freshIdGen: Counter, instId: Int): ConstraintType<Elab> = ElabConstrV(v, instId)
    override fun variableNames() = setOf(v)
}

object ElabL : Leaf<Elab> {
    override fun toString() = "L"
    override fun instantiate(freshIdGen: Counter, instId: Int): ConstraintType<Elab> = ElabConstrL
    override fun variableNames() = emptySet<Int>()
}

class ElabVarHole() : Hole<Elab>() {
    override fun toString() = "V_${holeId}_"
    override fun expansions(
        unification: Unification<Elab>,
        vars: Int,
        recursionBound: Int?
    ): List<Pair<SearchNode<Elab>, Commitment<Elab>>> =
        (0 until vars + 1).map { ElabV(it) }.map { it to (this to it) }

    // TODO Not sure if this does what I want to do.
//    override fun equals(other: Any?) = other is ElabVarHole
//    override fun hashCode() = 0
}

/** Good style would be to hide this constructor somehow so it can only be instantiated by ElabV */
data class ElabConstrV(val v: Int, val instId: Int) : Substitutable<Elab>() {
    override fun toString() = "V${v}-$instId"
}

object ElabConstrL : CTypeConstructor<Elab>(mutableListOf()) {
    override fun match(other: CTypeConstructor<Elab>): Boolean = other is ElabConstrL
    override fun toString() = "L"
}

private fun compileElabIntermediate(seed: Candidate<Elab>): Candidate<Elaborated> {
    ElaboratedL.reset()
    fun compile(seed: SearchNode<Elab>): SearchNode<Elaborated> = when (seed) {
        is ElabV -> ElaboratedV(seed.v)
        ElabL -> ElaboratedL.fresh()
        is NArrow -> NArrow(compile(seed.l), compile(seed.r), true)
        is Hole -> throw Exception("Invariant broken")
        else -> throw Exception("Will never happen due to types")
    }
    return Candidate(seed.names, seed.types.map { compile(it) })
}

object Elaborated : Language {
    val aritiesToDeps = mutableMapOf<List<Int>, DependencyAnalysis>()

    private var id = 0
    fun freshCandidateId() = id++
}

data class ElaboratedV(val v: Int) : Leaf<Elaborated> {
    override fun toString() = "V$v"
    override fun instantiate(freshIdGen: Counter, instId: Int): ConstraintType<Elaborated> =
        ElaboratedConstrV(v, instId)

    override fun variableNames() = setOf(v)
}

data class ElaboratedL(val label: Int) : Leaf<Elaborated> {
    companion object {
        private var lab = 0
        fun reset() {
            lab = 0
        }

        fun fresh() = ElaboratedL(lab++)
        fun fromString(s: String) = ElaboratedL(s.removePrefix("L").toInt())
    }

    override fun toString() = "L$label"
    override fun instantiate(freshIdGen: Counter, instId: Int): ConstraintType<Elaborated> = ElaboratedConstrL(label)
    override fun variableNames() = emptySet<Int>()
}

data class ElaboratedConstrV(val v: Int, val instId: Int) : Substitutable<Elaborated>() {
    override fun toString() = "V${v}-$instId"
}

data class ElaboratedConstrL(val label: Int) : CTypeConstructor<Elaborated>(mutableListOf()) {
    override fun match(other: CTypeConstructor<Elaborated>): Boolean = other is ElaboratedConstrL
    override fun toString() = "L$label"
    override fun split(other: CTypeConstructor<Elaborated>): List<Constraint<Elaborated>>? {
        return super.split(other)?.plus(LabelConstraint(label, (other as ElaboratedConstrL).label))
    }
}

data class LabelConstraint(val a: Int, val b: Int) : Constraint<Elaborated> {
    override fun toString() = "L$a == L$b"
    override fun trivial() = a == b
    override fun copy() = this
}

/** So ugly, but here since we have a new core. Later, delete old code. */
sealed interface Dependency

object NoVariables : Dependency {
    override fun toString() = "NoVariables"
}

data class Only(val v: Int) : Dependency {
    override fun toString(): String = "Only($v)"
}

data class MustContain(val vars: List<Int>) : Dependency {
    override fun toString(): String = "Contains$vars"
}

fun typeOfParam(candidate: Candidate<Elab>, param: ParameterNode): SearchNode<Elab> {
    var curr = candidate.types[candidate.names.indexOf(param.f)]
    var i = 0
    while (curr is NArrow<Elab>) {
        if (i == param.i) return curr.l
        curr = curr.r
        i++
    }
    assert(i == param.i)
    return curr
}

fun constraints(candidate: Candidate<Elab>, deps: DependencyAnalysis): Map<ParameterNode, Dependency> {
    val constraints = mutableMapOf<ParameterNode, Dependency>()
    candidate.names.forEach { name ->
        val graph = deps.graphs[name]!!
        graph.loops.forEach {
            constraints[ParameterNode(name, it.node.i)] = NoVariables
        }
        graph.deps.forEach {
            val sup = typeOfParam(candidate, it.sup)
            if (sup is ElabV) constraints[ParameterNode(name, it.sub.i)] = Only(sup.v)
        }
        equivalenceClasses(graph.deps) { e1, e2 -> e1.sup == e2.sup }.forEach {
            val sink = it.first().sup
            val containedVars = it.map { typeOfParam(candidate, it.sub) }.filterIsInstance<ElabV>().map { it.v }
            if (typeOfParam(candidate, sink) !is Var && containedVars.isNotEmpty()) {
                val p = ParameterNode(name, sink.i)
                if (p !in constraints) constraints[p] = MustContain(containedVars)
            }
        }
    }
    return constraints
}

fun compileElab(
    seed: Candidate<Elab>,
    query: Query,
    oracle: Oracle,
    unification: UnificationForCandidate<Elaborated>,
    callSolver: Boolean
): Candidate<Concrete>? {
    val deps = Elaborated.aritiesToDeps.getOrPut(seed.arities()) {
        DependencyAnalysis(
            query,
            seed.names.zip(seed.arities()).toMap(),
            oracle
        )
    }

    val constraints = constraints(seed, deps)

    fun satisfiesDependencies(): Boolean {
        val params = seed.types.map { seed.params(it) }
        return constraints.all { (param, dep) ->
            val t = params[seed.names.indexOf(param.f)][param.i]
            when (dep) {
                is MustContain -> (t !is ElabV) || (dep.vars.size == 1 && t.v == dep.vars[0])
                NoVariables -> t !is ElabV
                is Only -> (t !is ElabV) || (dep.v == t.v)
            }
        }
    }

    if (!satisfiesDependencies()) {
        return null  // TODO these should really be pruned before the fn call, maybe even while enuming Elab
        // dependencies should just be the edges between parameter nodes,
        // we decide for a given type whether it satisfies the edges. no need for constraint middle man
    }

    val elaborated = compileElabIntermediate(seed)
    val uf = IntUnionFind()
    (unification(elaborated, query.posExsBeforeSubexprs).constraints()?.filterIsInstance<LabelConstraint>()
        ?: throw Exception("Invariant broken")).forEach {
        uf.union(it.a, it.b)
    }

    // TODO this is very hacky. Need it to collect little ones like 0 = 1
    elaborated.assocList.forEachIndexed { i, (n1, t1) ->
        elaborated.assocList.forEachIndexed { j, (n2, t2) ->
            if (i < j && t1 is ElaboratedL && t2 is ElaboratedL && oracle.equal(Name(n1), Name(n2)))
                uf.union(t1.label, t2.label)
        }
    }

    fun amendWithEquivs(node: SearchNode<Elaborated>): SearchNode<Elaborated> = when (node) {
        is ElaboratedL -> ElaboratedL(uf.find(node.label) ?: node.label)
        is NArrow -> NArrow(amendWithEquivs(node.l), amendWithEquivs(node.r), true)
        is ElaboratedV -> node
        else -> throw Exception("Impossible")
    }

    val elaboratedAfterEquivalences = Candidate(elaborated.names, elaborated.types.map { amendWithEquivs(it) })

    val gen = LabelArityConstraints(elaboratedAfterEquivalences, deps)
    val seedId = Elaborated.freshCandidateId()
    if (callSolver) callCVC(gen.initialQuery(), "$seedId")

    var counter = 0
    var previousSolution = readCVC("$seedId") ?: return null
    var lastSuccessful = -1
    do {
//        println("Getting smaller CVC results")
        val parser = CVCParser(previousSolution)
        val testName = "$seedId-smaller${counter++}"
        val cont = if (parser.sizes.isNotEmpty()) callCVC(
            gen.smallerQuery(parser.sizes.mapKeys { gen.pySizeToL(it.key).label }),
            testName
        ) else false
        if (cont) {
            lastSuccessful = counter - 1
            previousSolution = readCVC(testName)!!  // callCVC returns success code stored in cont
        }
    } while (cont)
    val finalSuccessfulOutput = if (lastSuccessful == -1) "$seedId" else "$seedId-smaller$lastSuccessful"

    val labelArities: Map<Int, Int> =
        CVCParser(readCVC(finalSuccessfulOutput)!!).sizes.mapKeys { gen.pySizeToL(it.key).label }

    if (labelArities.values.all { it > 0 }) return null  // TODO I need to change if we allow L<a>
    fun compileParameter(node: SearchNode<Elaborated>, parameter: ParameterNode): SearchNode<Concrete> = when (node) {
        is ElaboratedV -> ConcreteV(node.v)
        is ElaboratedL -> ConcreteL(
            node.label,
            List(labelArities[node.label]!!) {  // TODO If unconstrained, 0 params?
                ConcreteHole(deps.mayHaveFresh(parameter), constraints[parameter], labelArities)
            })
        is NArrow -> NArrow(compileParameter(node.l, parameter), compileParameter(node.r, parameter), true)
        else -> throw Exception("Will never happen")
    }

    fun compile(name: String, paramsSoFar: Int, seed: SearchNode<Elaborated>): SearchNode<Concrete> = when (seed) {
        is ElaboratedV, is ElaboratedL -> compileParameter(seed, ParameterNode(name, paramsSoFar))
        is NArrow -> NArrow(
            compileParameter(seed.l, ParameterNode(name, paramsSoFar)),
            compile(name, paramsSoFar + 1, seed.r), false
        )
        is Hole -> throw Exception("Invariant broken")
        else -> throw Exception("Will never happen due to types")
    }

    return Candidate(
        elaboratedAfterEquivalences.names,
        elaboratedAfterEquivalences.names.zip(elaboratedAfterEquivalences.types)
            .map { (name, ty) -> compile(name, 0, ty) },
        constraints
    )
}

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
    // TODO We want to use the below equals when we are comparing new candidates against what we've seen before.
    //      but we want to use built in physical equals when we are looking to replace holes!
//    override fun equals(other: Any?): Boolean = other is ConcreteHole
//    override fun hashCode() = 0

    override fun expansions(
        unification: Unification<Concrete>,
        vars: Int,
        recursionBound: Int?
    ): List<Pair<SearchNode<Concrete>, Commitment<Concrete>>> =
        if (recursionBound != null && recursionBound <= 1) expansionsNoBound(unification, vars).filter {
            when (val t = it.first) {
                is ConcreteL -> t.params.isEmpty()
                is NArrow -> false
                is ConcreteHole -> true
                is ConcreteV -> true
                else -> throw Exception("Impossible")
            }
        } else expansionsNoBound(unification, vars)

    private fun hole() = ConcreteHole(mayHaveFresh, constraint, labelArities)
    private val fnExpansion by lazy { NArrow(hole(), hole(), true) }
    private val labelExpansions by lazy { labelArities.map { ConcreteL(it.key, List(it.value) { hole() }) } }

    private fun expansionsNoBound(
        unification: Unification<Concrete>,
        vars: Int,
    ): List<Pair<SearchNode<Concrete>, Commitment<Concrete>>> {
        fun wrap(e: List<SearchNode<Concrete>>) = e.map { it to (this to it) }

        val variableExpansions = when (constraint) {  // TODO weird that vars need to be sorted
            null, is MustContain -> (0 until (if (mayHaveFresh) vars + 1 else vars)).map { ConcreteV(it) }
            NoVariables -> listOf()
            is Only -> listOf(ConcreteV(constraint.v))
        }

        val mustBeCompatible = unification.holeEquals(this)

        if (mustBeCompatible.isNotEmpty()) {
            if (mustBeCompatible.any { a -> mustBeCompatible.any { b -> !a.match(b) } }) return wrap(variableExpansions)
            if (mustBeCompatible.first() is CArrow && mustBeCompatible.all {
                    mustBeCompatible.first().match(it)
                }) return wrap(listOf(fnExpansion))
//            if (mustBeCompatible.first() is ConcreteConstrL && mustBeCompatible.all {
//                    mustBeCompatible.first().match(it)
//                }) {
//                val label = (mustBeCompatible.first() as ConcreteConstrL).label
//                // TODO this is bad bc the holes are not shared... bad for priority assignment
//                return wrap(listOf(ConcreteL(label, List(labelArities[label]!!) { hole() })) + variableExpansions)
//            }
            // TODO can't do this for labels bc sometimes we have less constraints bc of lack of earlier commitments.
            //   we might erroneously commit to list of int bc we haven't yet committed to a different thing being list of bool.
            //   AH, but, *if* there is only one label here, the only label expansion we could have is that label!
            //       and we can say this recursively too
        }

        return wrap(  // TODO hilariously, I think the order makes a difference here. we should sort by size tbh
            labelExpansions + variableExpansions + fnExpansion
        )
    }

//    private fun antiunify(types: List<CTypeConstructor<Concrete>>): ConstraintType<Concrete>
}

data class ConcreteConstrV(val v: Int, val instId: Int) : Substitutable<Concrete>() {
    override fun toString() = "V${v}-$instId"
}

data class ConcreteConstrL(val label: Int, override val params: List<ConstraintType<Concrete>>) :
    CTypeConstructor<Concrete>(params) {
    companion object {
        fun new(label: Int, params: List<ConstraintType<Concrete>>) = ConcreteConstrL(label, params.toMutableList())
    }

    override fun match(other: CTypeConstructor<Concrete>): Boolean = other is ConcreteConstrL && label == other.label
    override fun toString() = "L$label$params"
}

object ConcreteSketch : Language

class Blank(
    mayHaveFresh: Boolean,
    constraint: Dependency?,
    labelArities: Map<Int, Int>,
) : SketchHole(mayHaveFresh, constraint, labelArities) {
    init {
        TODO(
            "It is a hole bc we want to be able to fast-forward." +
                    "We want it to have priority zero and only expand to itself"
        )
    }

    override fun conflict() = 0
    override fun priority() = 0
    override fun holes() = 1 // TODO not sure about this one
    override fun full() = false // TODO also not sure about this one

    override fun expansions(
        unification: Unification<ConcreteSketch>,
        vars: Int,
        recursionBound: Int?
    ): List<Pair<SearchNode<ConcreteSketch>, Commitment<ConcreteSketch>>> = listOf(this to null)
}

data class SketchV(val v: Int) : Leaf<ConcreteSketch> {
    override fun toString() = "V$v"
    override fun instantiate(freshIdGen: Counter, instId: Int): ConstraintType<ConcreteSketch> =
        SketchConstrV(v, instId)

    override fun variableNames() = setOf(v)
}

data class SketchL(val id: Int, override val params: List<SearchNode<ConcreteSketch>>) :
    Branch<ConcreteSketch>(params) {
    override fun toString() = "L$id$params"
    override fun instantiate(freshIdGen: Counter, instId: Int): ConstraintType<ConcreteSketch> =
        SketchConstrL.new(id, params.map { it.instantiate(freshIdGen, instId) })

    override fun replace(hole: Hole<ConcreteSketch>, node: SearchNode<ConcreteSketch>) =
        SketchL(id, params.map { it.replace(hole, node) })

    override fun replaceWithAll(
        hole: Hole<ConcreteSketch>,
        nodes: List<SearchNode<ConcreteSketch>>
    ): List<SearchNode<ConcreteSketch>> {
        val newParams = params.map { it.replaceWithAll(hole, nodes) }
        val changed = newParams.indexOfFirst { it.size > 1 }
        return newParams[changed].map {
            SketchL(id, params.mapIndexed { i, param -> if (i == changed) it else param })
        }
    }

    override fun dfsLeftExpansions(
        unification: Unification<ConcreteSketch>, vars: Int, recursionBound: Int?
    ): List<Pair<SearchNode<ConcreteSketch>, Commitment<ConcreteSketch>>> {
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
        unification: Unification<ConcreteSketch>, vars: Int, recursionBound: Int?
    ): List<Pair<SearchNode<ConcreteSketch>, Commitment<ConcreteSketch>>> {
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
) : Hole<ConcreteSketch>() {
    // TODO We want to use the below equals when we are comparing new candidates against what we've seen before.
    //      but we want to use built in physical equals when we are looking to replace holes!
//    override fun equals(other: Any?): Boolean = other is ConcreteHole
//    override fun hashCode() = 0

    override fun expansions(
        unification: Unification<ConcreteSketch>,
        vars: Int,
        recursionBound: Int?
    ): List<Pair<SearchNode<ConcreteSketch>, Commitment<ConcreteSketch>>> =
        if (recursionBound != null && recursionBound <= 1) expansionsNoBound(unification, vars).filter {
            when (val t = it.first) {
                is SketchL -> t.params.isEmpty()
                is NArrow -> false
                is SketchHole -> true
                is SketchV -> true
                is Blank -> true
                else -> throw Exception("Impossible")
            }
        } else expansionsNoBound(unification, vars)

    private fun hole() = SketchHole(mayHaveFresh, constraint, labelArities)
    private val fnExpansion by lazy { NArrow(hole(), hole(), true) }
    private val labelExpansions by lazy { labelArities.map { SketchL(it.key, List(it.value) { hole() }) } }
    private val blankExpansion by lazy { Blank(mayHaveFresh, constraint, labelArities) }

    private fun expansionsNoBound(
        unification: Unification<ConcreteSketch>,
        vars: Int,
    ): List<Pair<SearchNode<ConcreteSketch>, Commitment<ConcreteSketch>>> {
        fun wrap(e: List<SearchNode<ConcreteSketch>>) = e.map { it to (this to it) }

        val variableExpansions = when (constraint) {  // TODO weird that vars need to be sorted
            null, is MustContain -> (0 until (if (mayHaveFresh) vars + 1 else vars)).map { SketchV(it) }
            NoVariables -> listOf()
            is Only -> listOf(SketchV(constraint.v))
        }

        val mustBeCompatible = unification.holeEquals(this)

        if (mustBeCompatible.isNotEmpty()) {
            if (mustBeCompatible.any { a -> mustBeCompatible.any { b -> !a.match(b) } }) return wrap(variableExpansions)
            if (mustBeCompatible.first() is CArrow && mustBeCompatible.all {
                    mustBeCompatible.first().match(it)
                }) return wrap(listOf(fnExpansion))
//            if (mustBeCompatible.first() is ConcreteConstrL && mustBeCompatible.all {
//                    mustBeCompatible.first().match(it)
//                }) {
//                val label = (mustBeCompatible.first() as ConcreteConstrL).label
//                // TODO this is bad bc the holes are not shared... bad for priority assignment
//                return wrap(listOf(ConcreteL(label, List(labelArities[label]!!) { hole() })) + variableExpansions)
//            }
            // TODO can't do this for labels bc sometimes we have less constraints bc of lack of earlier commitments.
            //   we might erroneously commit to list of int bc we haven't yet committed to a different thing being list of bool.
            //   AH, but, *if* there is only one label here, the only label expansion we could have is that label!
            //       and we can say this recursively too
        }

        return wrap(  // TODO hilariously, I think the order makes a difference here. we should sort by size tbh
            listOf(blankExpansion) + labelExpansions + variableExpansions + fnExpansion
        )
    }

//    private fun antiunify(types: List<CTypeConstructor<Concrete>>): ConstraintType<Concrete>
}

data class SketchConstrV(val v: Int, val instId: Int) : Substitutable<ConcreteSketch>() {
    override fun toString() = "V${v}-$instId"
}

data class SketchConstrL(val label: Int, override val params: List<ConstraintType<ConcreteSketch>>) :
    CTypeConstructor<ConcreteSketch>(params) {
    companion object {
        fun new(label: Int, params: List<ConstraintType<ConcreteSketch>>) = SketchConstrL(label, params.toMutableList())
    }

    override fun match(other: CTypeConstructor<ConcreteSketch>): Boolean =
        other is SketchConstrL && label == other.label

    override fun toString() = "L$label$params"
}
