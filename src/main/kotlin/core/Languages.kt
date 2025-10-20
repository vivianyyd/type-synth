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
    override fun expansions(
        constrs: List<Constraint<Init>>,
        vars: Set<Int>,
        recursionBound: Int?
    ): List<Pair<SearchNode<Init>, Commitment<Init>>> =
        (listOf(InitV, InitL) + (if (recursionBound != null && recursionBound <= 1) listOf()
        else listOf(
            NArrow(InitHole(), InitHole(), true)
        ))).map { it to (this to it) }
}

object InitConstrV : CVariable<Init> {
    override fun toString() = "V"
}

object InitConstrL : CTypeConstructor<Init>(mutableListOf()) {
    override fun match(other: CTypeConstructor<Init>): Boolean = other is InitConstrL
    override fun toString() = "L"
}

fun compileInit(seed: Candidate<Init>): Candidate<Elab> {
    fun compile(seed: SearchNode<Init>, vars: Int): Pair<SearchNode<Elab>, Int> = when (seed) {
        is NArrow -> {
            val (leftTy, leftVars) = compile(seed.l, vars)
            val (rightTy, endVars) = compile(seed.r, leftVars)
            NArrow(leftTy, rightTy, true) to endVars
        }
        InitL -> ElabL to vars
        InitV -> ElabVarHole((0..vars).toList()) to vars + 1
        is InitHole -> throw Exception("Invariant broken")
        else -> throw Exception("Will never happen due to types")
    }
    return Candidate(seed.names, seed.types.map { compile(it, 0).first })
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

class ElabVarHole(val vars: List<Int>) : Hole<Elab>() {
    override fun toString() = "V_"
    override fun expansions(
        constrs: List<Constraint<Elab>>,
        vars: Set<Int>,
        recursionBound: Int?
    ): List<Pair<SearchNode<Elab>, Commitment<Elab>>> =
        this.vars.map { ElabV(it) }.map { it to (this to it) }

    // TODO Not sure if this does what I want to do.
//    override fun equals(other: Any?) = other is ElabVarHole
//    override fun hashCode() = 0
}

/** Good style would be to hide this constructor somehow so it can only be instantiated by ElabV */
data class ElabConstrV(val v: Int, val instId: Int) : CVariable<Elab>, Substitutable<Elab> {
    override fun toString() = "V${v}_$instId"
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

data class ElaboratedConstrV(val v: Int, val instId: Int) : CVariable<Elaborated>, Substitutable<Elaborated> {
    override fun toString() = "V${v}_$instId"
}

data class ElaboratedConstrL(val label: Int) : CTypeConstructor<Elaborated>(mutableListOf()) {
    override fun match(other: CTypeConstructor<Elaborated>): Boolean = other is ElaboratedConstrL
    override fun toString() = "L"
    override fun split(other: CTypeConstructor<Elaborated>): List<Constraint<Elaborated>>? {
        return super.split(other)?.plus(LabelConstraint(label, (other as ElaboratedConstrL).label))
    }
}

data class LabelConstraint(val a: Int, val b: Int) : Constraint<Elaborated> {
    override fun toString() = "L$a == L$b"
    override fun trivial() = a == b
}

/** So ugly, but here since we have a new core. Later, delete old code. */
sealed interface Dependency

object NoVariables : Dependency
data class Only(val v: Int) : Dependency
data class MustContain(val vars: List<Int>) : Dependency

fun typeOfParam(candidate: Candidate<Elaborated>, param: ParameterNode): SearchNode<Elaborated> {
    var curr = candidate.types[candidate.names.indexOf(param.f)]
    var i = 0
    while (curr is NArrow<Elaborated>) {
        if (i == param.i) return curr.l
        curr = curr.r
        i++
    }
    assert(i == param.i)
    return curr
}

fun constraints(candidate: Candidate<Elaborated>, deps: DependencyAnalysis): Map<ParameterNode, Dependency> {
    val constraints = mutableMapOf<ParameterNode, Dependency>()
    candidate.names.forEach { name ->
        val graph = deps.graphs[name]!!
        graph.loops.forEach {
            constraints[ParameterNode(name, it.node.i)] = NoVariables
        }
        graph.deps.forEach {
            val sup = typeOfParam(candidate, it.sup)
            if (sup is ElaboratedV) constraints[ParameterNode(name, it.sub.i)] = Only(sup.v)
        }
        equivalenceClasses(graph.deps) { e1, e2 -> e1.sup == e2.sup }.forEach {
            val sink = it.first().sup
            val containedVars =
                it.map { typeOfParam(candidate, it.sub) }.filterIsInstance<ElaboratedV>().map { it.v }
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
    oracle: EqualityNewOracle,
    callSolver: Boolean
): Candidate<Concrete>? {
    val deps = Elaborated.aritiesToDeps.getOrPut(seed.arities()) {
        DependencyAnalysis(
            query,
            seed.names.zip(seed.arities()).toMap(),
            oracle
        )
    }

    val elaborated = compileElabIntermediate(seed)
    val uf = TUnionFind()
    (Unification(elaborated, query.posExsBeforeSubexprs).get()?.filterIsInstance<LabelConstraint>()
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
        println("Getting smaller CVC results")
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

    println(elaboratedAfterEquivalences)
    println(labelArities)

    val constraints = constraints(elaboratedAfterEquivalences, deps)

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
            .map { (name, ty) -> compile(name, 0, ty) })
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

    override fun bfsExpansions(
        constrs: List<Constraint<Concrete>>,
        vars: Set<Int>,
        recursionBound: Int?
    ): List<Pair<SearchNode<Concrete>, Commitment<Concrete>>> =
        params.indices.flatMap { i ->
            params[i].bfsExpansions(constrs, vars, recursionBound?.let { it - 1 })
                .map { (node, commit) ->
                    ConcreteL(
                        id,
                        params.mapIndexed { j, p -> if (j == i) node else p }) to commit
                }
        } + (if (params.isEmpty()) listOf(this to null) else listOf())

    override fun dfsLeftExpansions(
        constrs: List<Constraint<Concrete>>, vars: Set<Int>, recursionBound: Int?
    ): List<Pair<SearchNode<Concrete>, Commitment<Concrete>>> {
        var cont = true
        return params.indices.flatMap { i ->
            if (cont) {
                val exp =
                    params[i].dfsLeftExpansions(constrs, vars, recursionBound?.let { it - 1 }).map { (node, commit) ->
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
        constrs: List<Constraint<Concrete>>,
        vars: Set<Int>,
        recursionBound: Int?
    ): List<Pair<SearchNode<Concrete>, Commitment<Concrete>>> =
        if (recursionBound != null && recursionBound <= 1) expansionsNoBound(constrs, vars).filter {
            when (val t = it.first) {
                is ConcreteL -> t.params.isEmpty()
                is NArrow -> false
                is ConcreteHole -> true
                is ConcreteV -> true
                else -> throw Exception("Impossible")
            }
        } else expansionsNoBound(constrs, vars)

    private fun expansionsNoBound(
        constrs: List<Constraint<Concrete>>,
        vars: Set<Int>,
    ): List<Pair<SearchNode<Concrete>, Commitment<Concrete>>> {
        fun hole() = ConcreteHole(mayHaveFresh, constraint, labelArities)
        fun wrap(e: List<SearchNode<Concrete>>) = e.map { it to (this to it) }

        val variableExpansions = when (constraint) {  // TODO weird that vars need to be sorted
            null, is MustContain -> (if (mayHaveFresh) vars + (vars.size + 1) else vars).sorted().map { ConcreteV(it) }
            NoVariables -> listOf()
            is Only -> listOf(ConcreteV(constraint.v))
        }
        val fnExpansion = NArrow(hole(), hole(), true)

        val mustBeCompatible = constrs.filterIsInstance<EqualityConstraint<Concrete>>().mapNotNull {
            if (it.l is Instantiation && (it.l as Instantiation<Concrete>).n == this) it.r
            else if (it.r is Instantiation && (it.r as Instantiation<Concrete>).n == this) it.l
            else null
        }.filterIsInstance<CTypeConstructor<Concrete>>()

        if (mustBeCompatible.isNotEmpty()) {
            if (mustBeCompatible.any { a -> mustBeCompatible.any { b -> !a.match(b) } }) return wrap(variableExpansions)
            if (mustBeCompatible.all { mustBeCompatible.first().match(it) }) return wrap(
                when (val f = mustBeCompatible.first()) {
                    is CArrow -> listOf(fnExpansion)
                    is ConcreteConstrL -> listOf(ConcreteL(f.label, List(labelArities[f.label]!!) { hole() }))
                    else -> throw Exception("Cannot happen due to types")
                }
            )
        }

        return wrap(  // TODO hilariously, I think the order makes a difference here. we should sort by size tbh
            variableExpansions + labelArities.map { ConcreteL(it.key, List(it.value) { hole() }) } + fnExpansion
        )
    }
}

data class ConcreteConstrV(val v: Int, val instId: Int) : CVariable<Concrete>, Substitutable<Concrete> {
    override fun toString() = "V${v}_$instId"
}

data class ConcreteConstrL(val label: Int, override val params: MutableList<ConstraintType<Concrete>>) :
    CTypeConstructor<Concrete>(params) {
    companion object {
        fun new(label: Int, params: List<ConstraintType<Concrete>>) = ConcreteConstrL(label, params.toMutableList())
    }

    override fun match(other: CTypeConstructor<Concrete>): Boolean = other is ConcreteConstrL && label == other.label
    override fun toString() = "L$label$params"
}
