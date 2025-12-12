package core.languages

import core.LabelArityConstraints
import core.unification.*
import dependencyanalysis.DependencyAnalysis
import query.Name
import query.Query
import stc.Var
import util.*

sealed interface Language

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

fun compileToConcrete(info: ElaboratedInfo, emitBlanks: Boolean) =
    Candidate(
        info.candidate.names,
        info.candidate.names.zip(info.candidate.types).map { (name, ty) ->
            compileConcreteType(name, 0, ty, info.labelArities, info.deps, info.constraints, emitBlanks)
        })

fun compileConcreteParameter(
    node: SearchNode<Elaborated>,
    parameter: ParameterNode,
    labelArities: Map<Int, Int>,
    deps: DependencyAnalysis,
    constraints: Map<ParameterNode, Dependency>,
    emitBlanks: Boolean
): SearchNode<Concrete> = when (node) {
    is ElaboratedV -> ConcreteV(node.v)
    is ElaboratedL -> ConcreteL(
        node.label,
        List(labelArities[node.label]!!) {  // TODO If unconstrained, 0 params?
            ConcreteHole(deps.mayHaveFresh(parameter), constraints[parameter], labelArities, emitBlanks)
        })
    is NArrow -> NArrow(
        compileConcreteParameter(node.l, parameter, labelArities, deps, constraints, emitBlanks),
        compileConcreteParameter(node.r, parameter, labelArities, deps, constraints, emitBlanks),
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
    constraints: Map<ParameterNode, Dependency>,
    emitBlanks: Boolean
): SearchNode<Concrete> = when (seed) {
    is ElaboratedV, is ElaboratedL -> compileConcreteParameter(
        seed,
        ParameterNode(name, paramsSoFar),
        labelArities,
        deps,
        constraints,
        emitBlanks
    )
    is NArrow -> NArrow(
        compileConcreteParameter(seed.l, ParameterNode(name, paramsSoFar), labelArities, deps, constraints, emitBlanks),
        compileConcreteType(name, paramsSoFar + 1, seed.r, labelArities, deps, constraints, emitBlanks), false
    )
    is Hole -> throw Exception("Invariant broken")
    else -> throw Exception("Will never happen due to types")
}
