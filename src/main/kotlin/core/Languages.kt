package core

import util.Counter

object Init : Language

object InitV : Leaf<Init> {
    override fun toString() = "V"
    override fun instantiate(i: Counter, insts: Int): ConstraintType<Init> = InitConstrV
    override fun variableNames() = emptySet<Int>()
}

object InitL : Leaf<Init> {
    override fun toString() = "L"
    override fun instantiate(i: Counter, insts: Int): ConstraintType<Init> = InitConstrL
    override fun variableNames() = emptySet<Int>()
}

class InitHole : Hole<Init>() {
    override fun expansions(constrs: List<Constraint<Init>>): List<Pair<SearchNode<Init>, Commitment<Init>>> =
        listOf(NArrow(InitHole(), InitHole()), InitV, InitL).map { it to (this to it) }
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
            NArrow(leftTy, rightTy) to endVars
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
    override fun instantiate(i: Counter, insts: Int): ConstraintType<Elab> = ElabConstrV(v, insts)
    override fun variableNames() = setOf(v)
}

object ElabL : Leaf<Elab> {
    override fun toString() = "L"
    override fun instantiate(i: Counter, insts: Int): ConstraintType<Elab> = ElabConstrL
    override fun variableNames() = emptySet<Int>()
}

data class ElabVarHole(val vars: List<Int>) : Hole<Elab>() {
    override fun toString() = "V_"
    override fun expansions(constrs: List<Constraint<Elab>>): List<Pair<SearchNode<Elab>, Commitment<Elab>>> =
        vars.map { ElabV(it) }.map { it to (this to it) }
}

/*
//data class ElabLabHole(val id: Int) : Hole<Elab>() {
//    companion object {
//        var fresh = 0
//
//        fun fresh() = ElabL(fresh++)
//    }
//
//    override fun toString() = "L_$id"
//
//    override fun expansions(constrs: List<Constraint<Elab>>): List<Pair<SearchNode<Elab>, Commitment<Elab>>> {
//        val uf = TUnionFind()
//        constrs.filterIsInstance<LabelConstraint>().forEach {
//            uf.union(it.a, it.b)
//        }
//        label = uf.find(label)
//        println("my label is $label and i found in UF ${uf.find(label)}")
//        return listOf(ElabL(uf.find(label)) to null)
//    }
//}

//data class ElabConstrL(val label: Int) : CTypeConstructor<Elab>(mutableListOf()) {
//    override fun match(other: CTypeConstructor<Elab>): Boolean = other is ElabConstrL
//    override fun split(other: CTypeConstructor<Elab>): List<Constraint<Elab>>? {
//        return super.split(other)?.plus(LabelConstraint(label, (other as ElabConstrL).label))
//    }
//
//    override fun toString() = "L$label"
//}
 */

data class LabelConstraint(val a: Int, val b: Int) : Constraint<Elab> {
    override fun toString() = "L$a == L$b"
}

/** Good style would be to hide this constructor somehow so it can only be instantiated by ElabV */
data class ElabConstrV(val v: Int, val instId: Int) : CVariable<Elab>, Substitutable {
    override fun toString() = "V${v}_$instId"
}

object ElabConstrL : CTypeConstructor<Elab>(mutableListOf()) {
    override fun match(other: CTypeConstructor<Elab>): Boolean = other is ElabConstrL
    override fun toString() = "L"
}

/**
 * Two options for representing label assignments:
 * 1. We can have label holes, which init to having all previously init labels as options.
 *    Then, our unification algorithm is pure and fails on two labels if they differ.
 *    I guess we also have to reset the num labels to 0 for each new candidate here (same as below)
 * 2. We have no label holes; every L from Init gets a distinct name. Then we have an effectful unification algo,
 *    which forms equivalence classes. Then we use these to produce the next round of seeds.
 *    One important thing here is that we need to reset the UnionFind data structure for each seed candidate
 *    in the Elab level... Things get messy.
 *
 *  Actually the union find DS has to be init once for each Unification instance, so it can't just be upon compilation
 *  since expansions produces new var bindings
 *
 *  For both options, the reset can be done in a translateCandidate() fn so it's not horrible either way. UF faster
 * */
/*
//data class ElabLabHole private constructor(val labelsBefore: Int) : Hole<Elab>() {
//    companion object {
//        var nLabels = 0
//
//        fun reset() {
//            nLabels = 0
//        }
//    }
//
//    constructor() : this(nLabels++)
//
//    override fun toString() = "L_"
//    override fun expansions(): List<Pair<SearchNode<Elab>, Commitment<Elab>>> =
//        (0..labelsBefore).map { ElabL(it) }.map { it to (this to it) }
//}
//
//data class ElabConstrL(val label: Int) : CTypeConstructor<Elab>(mutableListOf()) {
//    override fun match(other: CTypeConstructor<Elab>): Boolean = other is ElabConstrL && other.label == label
//}
*/

fun compileElab(seed: Candidate<Elab>): Candidate<Concrete> {
    TODO()
//    fun compile(seed: SearchNode<Init>, vars: Int): Pair<SearchNode<Elab>, Int> = when (seed) {
//        is NArrow -> {
//            val (leftTy, leftVars) = compile(seed.l, vars)
//            val (rightTy, endVars) = compile(seed.r, leftVars)
//            NArrow(leftTy, rightTy) to endVars
//        }
//        InitL -> ElabL to vars
//        InitV -> ElabVarHole((0..vars).toList()) to vars + 1
//        is InitHole -> throw Exception("Invariant broken")
//        else -> throw Exception("Will never happen due to types")
//    }
//    return Candidate(seed.names, seed.types.map { compile(it, 0).first })
}

object Concrete : Language

/** ConcreteNode interface - helps maintain what variables have already been chosen in the type.
 * We need a way to check alpha equivalence */

data class ConcreteV(val v: Int) : Leaf<Concrete> {
    override fun toString() = "V$v"
    override fun instantiate(i: Counter, insts: Int): ConstraintType<Concrete> = ConcreteConstrV(v, insts)
    override fun variableNames() = setOf(v)
}

data class ConcreteL(override val params: List<SearchNode<Concrete>>) : Branch<Concrete>(params) {
    override fun instantiate(i: Counter, insts: Int): ConstraintType<Concrete> =
        ConcreteConstrL.new(params.map { it.instantiate(i, insts) })

    override fun expansions(constrs: List<Constraint<Concrete>>): List<Pair<SearchNode<Concrete>, Commitment<Concrete>>> =
        params.indices.flatMap { i ->
            params[i].expansions(constrs)
                .map { (node, commit) -> ConcreteL(params.mapIndexed { j, p -> if (j == i) node else p }) to commit }
        }
}

class ConcreteHole : Hole<Concrete>() {
    companion object {
        val labels = mutableMapOf<Int, Int>()  // label to arity
    }

    override fun expansions(constrs: List<Constraint<Concrete>>): List<Pair<SearchNode<Concrete>, Commitment<Concrete>>> =
        (listOf(
            NArrow(ConcreteHole(), ConcreteHole()),
            ConcreteV(TODO())
        ) + labels.map { (label, arity) -> ConcreteL(List(arity) { ConcreteHole() }) })
            .map { it to (this to it) }
}

data class ConcreteConstrV(val v: Int, val instId: Int) : CVariable<Concrete>, Substitutable {
    override fun toString() = "V${v}_$instId"
}

data class ConcreteConstrL(override val params: MutableList<ConstraintType<Concrete>>) :
    CTypeConstructor<Concrete>(params) {
    companion object {
        fun new(params: List<ConstraintType<Concrete>>) = ConcreteConstrL(params.toMutableList())
    }

    override fun match(other: CTypeConstructor<Concrete>): Boolean = other is ConcreteConstrL
    override fun toString() = "L"
}
