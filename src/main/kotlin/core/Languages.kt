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
        mustBeLeaf: Boolean
    ): List<SearchNode<Init>> {
        val mustBeCompatible = unification.holeEqualsConstructors(this)
        val fn = if (mustBeLeaf) listOf()
        else if (mustBeCompatible.any { it is CArrow }) listOf(fnExpansion) else listOf()
        return listOf(InitV, InitL) + fn
    }

    override fun fastForward(unification: Unification<Init>, vars: Int): SearchNode<Init>? = null
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

class ElabVarHole : Hole<Elab>() {
    override fun toString() = "V_${holeId}_"
    override fun expansions(
        unification: Unification<Elab>,
        vars: Int,
        mustBeLeaf: Boolean
    ): List<SearchNode<Elab>> =
        (0 until vars + 1).map { ElabV(it) }

    override fun fastForward(unification: Unification<Elab>, vars: Int): SearchNode<Elab>? = null

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

fun compileElabToInfo(
    seed: Candidate<Elab>,
    query: Query,
    oracle: Oracle,
    unification: UnificationForCandidate<Elaborated>,
    callSolver: Boolean
): ElaboratedInfo? {
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

    return ElaboratedInfo(elaboratedAfterEquivalences, labelArities, deps, constraints)
}

data class ElaboratedInfo(
    val candidate: Candidate<Elaborated>,
    val labelArities: Map<Int, Int>,
    val deps: DependencyAnalysis,
    val constraints: Map<ParameterNode, Dependency>
)

fun compileToConcrete(info: ElaboratedInfo) =
    Candidate(
        info.candidate.names,
        info.candidate.names.zip(info.candidate.types).map { (name, ty) ->
            compileConcreteType(name, 0, ty, info.labelArities, info.deps, info.constraints)
        })

fun compileConcreteParameter(
    node: SearchNode<Elaborated>,
    parameter: ParameterNode,
    labelArities: Map<Int, Int>,
    deps: DependencyAnalysis,
    constraints: Map<ParameterNode, Dependency>
): SearchNode<Concrete> = when (node) {
    is ElaboratedV -> ConcreteV(node.v)
    is ElaboratedL -> ConcreteL(
        node.label,
        List(labelArities[node.label]!!) {  // TODO If unconstrained, 0 params?
            ConcreteHole(deps.mayHaveFresh(parameter), constraints[parameter], labelArities)
        })
    is NArrow -> NArrow(
        compileConcreteParameter(node.l, parameter, labelArities, deps, constraints),
        compileConcreteParameter(node.r, parameter, labelArities, deps, constraints),
        true
    )
    else -> throw Exception("Will never happen")
}

fun compileConcreteType(
    name: String,
    paramsSoFar: Int,
    seed: SearchNode<Elaborated>,
    labelArities: Map<Int, Int>,
    deps: DependencyAnalysis,
    constraints: Map<ParameterNode, Dependency>
): SearchNode<Concrete> = when (seed) {
    is ElaboratedV, is ElaboratedL -> compileConcreteParameter(
        seed,
        ParameterNode(name, paramsSoFar),
        labelArities,
        deps,
        constraints
    )
    is NArrow -> NArrow(
        compileConcreteParameter(seed.l, ParameterNode(name, paramsSoFar), labelArities, deps, constraints),
        compileConcreteType(name, paramsSoFar + 1, seed.r, labelArities, deps, constraints), false
    )
    is Hole -> throw Exception("Invariant broken")
    else -> throw Exception("Will never happen due to types")
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

fun compileToSketch(info: ElaboratedInfo) =
    Candidate(
        info.candidate.names,
        info.candidate.names.zip(info.candidate.types).map { (name, ty) ->
            compileSketchType(name, 0, ty, info.labelArities, info.deps, info.constraints)
        })

fun compileSketchParameter(
    node: SearchNode<Elaborated>,
    parameter: ParameterNode,
    labelArities: Map<Int, Int>,
    deps: DependencyAnalysis,
    constraints: Map<ParameterNode, Dependency>
): SearchNode<Sketch> = when (node) {
    is ElaboratedV -> SketchV(node.v)
    is ElaboratedL -> SketchL(
        node.label,
        List(labelArities[node.label]!!) {  // TODO If unconstrained, 0 params?
            SketchHole(deps.mayHaveFresh(parameter), constraints[parameter], labelArities)
        })
    is NArrow -> NArrow(
        compileSketchParameter(node.l, parameter, labelArities, deps, constraints),
        compileSketchParameter(node.r, parameter, labelArities, deps, constraints),
        true
    )
    else -> throw Exception("Will never happen")
}

fun compileSketchType(
    name: String,
    paramsSoFar: Int,
    seed: SearchNode<Elaborated>,
    labelArities: Map<Int, Int>,
    deps: DependencyAnalysis,
    constraints: Map<ParameterNode, Dependency>
): SearchNode<Sketch> = when (seed) {
    is ElaboratedV, is ElaboratedL -> compileSketchParameter(
        seed,
        ParameterNode(name, paramsSoFar),
        labelArities,
        deps,
        constraints
    )
    is NArrow -> NArrow(
        compileSketchParameter(seed.l, ParameterNode(name, paramsSoFar), labelArities, deps, constraints),
        compileSketchType(name, paramsSoFar + 1, seed.r, labelArities, deps, constraints), false
    )
    is Hole -> throw Exception("Invariant broken")
    else -> throw Exception("Will never happen due to types")
}

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

data class SketchConstrV(val v: Int, val instId: Int) : Substitutable<Sketch>() {
    override fun toString() = "V${v}-$instId"
}

data class SketchConstrL(val label: Int, override val params: List<ConstraintType<Sketch>>) :
    CTypeConstructor<Sketch>(params) {
    companion object {
        fun new(label: Int, params: List<ConstraintType<Sketch>>) = SketchConstrL(label, params.toMutableList())
    }

    override fun match(other: CTypeConstructor<Sketch>): Boolean =
        other is SketchConstrL && label == other.label

    override fun toString() = "L$label$params"
}
