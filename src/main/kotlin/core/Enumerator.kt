package core

import query.App
import query.Name
import query.Query
import test.ConsTest
import util.Counter
import util.TUnionFind
import util.lazyCartesianProduct
import java.util.*

class Enumerator<L : Language>(val query: Query, seedCandidate: Candidate<L>) {
    val frontier = PriorityQueue<Candidate<L>>(compareBy({ it.depth }, { it.size }))
    val seen = mutableSetOf<Candidate<L>>()

    init {
        frontier.add(seedCandidate)
    }

    val ok = mutableListOf<Candidate<L>>() // TODO THIS WILL BE ONLY CONCRETE ONES

    var eCandidateCount = 0
    var eGeneratedDuplicate = 0
    var rejectedCandidate = 0

    fun enumerate(maxDepth: Int): List<Candidate<L>> {
        var curr: Candidate<L>
        do {
            curr = frontier.remove()

            println(curr)

            val constrs = Unification(curr, query.posExsBeforeSubexprs).get()


            println(constrs)


            // TODO We will often rediscover the same constraints even if two candidates are not identical...
            //      also, refinements of simpler candidates inherit their constraints, but we don't keep that state
            if (constrs != null) {
                val exp = curr.expansions(constrs).filter {
                    eCandidateCount++
                    val unseen = it !in seen
                    if (!unseen) eGeneratedDuplicate++
                    unseen
                }.toList()

                frontier.addAll(exp)
                seen.addAll(exp)
                if (curr.full() && curr.canonical()) ok.add(curr)
            } else rejectedCandidate++
        } while (curr.depth <= maxDepth && frontier.isNotEmpty())

        println("Candidates enumerated: $eCandidateCount")
        println("Duplicate candidates: $eGeneratedDuplicate")
        println("Candidates rejected: $rejectedCandidate")

        println("Accepted candidates: ${ok.size}")
        println("Frontier: ${frontier.size}")
        return ok
    }
}

fun main() {
    val q = ConsTest.query
    val inits = lazyCartesianProduct(q.names.map { name ->
        InitHole().expansions().map { it.first }
            .filter { it is InitL || (it is NArrow && q.posExamples.any { it is App && it.fn is Name && it.fn.name == name }) }
    })
    // TODO one optimization: We can see if our candidate is a refinement of a previously rejected one
    //      if multiple things share structure, their antiunifier may be the conflict

    val answers = inits.flatMap {
        println("Seed: $it")
        val e = Enumerator(ConsTest.query, Candidate(q.names, it))
        e.enumerate(3)
    }

    println(answers.toList().joinToString(prefix = "SOLUTIONS:\n", separator = "\n"))

    println("\n\n\n")

    val nextAnswers = answers.flatMap {
        println("Seed: $it")
        val e = Enumerator(ConsTest.query, compile(it))
        e.enumerate(3)
    }

    println(nextAnswers.toList().joinToString(prefix = "SOLUTIONS:\n", separator = "\n"))

    TODO(
        "In the next step, should we allow new labels to be introduced in expansions? " + "Will there ever be problems where a label type only occurs within other label types as a param?"
    )
}

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

fun compile(seed: Candidate<Init>): Candidate<Elab> {
    fun compile(seed: SearchNode<Init>, vars: Int): Pair<SearchNode<Elab>, Int> = when (seed) {
        is NArrow -> {
            val (leftTy, leftVars) = compile(seed.l, vars)
            val (rightTy, endVars) = compile(seed.r, leftVars)
            NArrow(leftTy, rightTy) to endVars
        }
        InitL -> ElabLabHole.fresh() to vars
        InitV -> ElabVarHole((0..vars).toList()) to vars + 1
        is InitHole -> throw Exception("Invariant broken")
        else -> throw Exception("Will never happen due to types")
    }
    return Candidate(seed.names, seed.types.map { compile(it, 0).first })
}

object Elab : Language

data class ElabV(val v: Int) : Leaf<Elab> {
    override fun toString() = "V$v"
    override fun instantiate(i: Counter, insts: Int): ConstraintType<Elab> = ElabConstrV(v, insts)
    override fun variableNames() = setOf(v)

}

data class ElabL(val label: Int) : Leaf<Elab> {
    override fun toString() = "L$label"
    override fun instantiate(i: Counter, insts: Int): ConstraintType<Elab> = ElabConstrL(label)
    override fun variableNames() = emptySet<Int>()
}

data class ElabVarHole(val vars: List<Int>) : Hole<Elab>() {
    override fun toString() = "V_"
    override fun expansions(constrs: List<Constraint<Elab>>): List<Pair<SearchNode<Elab>, Commitment<Elab>>> =
        vars.map { ElabV(it) }.map { it to (this to it) }
}

data class ElabLabHole(val label: Int) : Hole<Elab>() {
    companion object {
        var fresh = 0

        fun fresh() = ElabL(fresh++)
    }

    /**
     * union find inside constraint list
     * just make new type of Constraint for label names being equal. simplify() puts them into Union Find.
     * then when we do expansions, use that
     */

    override fun toString() = "L_${label}_"
    override fun expansions(constrs: List<Constraint<Elab>>): List<Pair<SearchNode<Elab>, Commitment<Elab>>> {
        val uf = TUnionFind<Int>()
        constrs.filterIsInstance<LabelConstraint>().forEach {
            uf.union(it.a, it.b)
        }
        return listOf(ElabL(uf.find(label))).map { it to (this to it) }
    }
}

data class ElabConstrL(val label: Int) : CTypeConstructor<Elab>(mutableListOf()) {
    override fun match(other: CTypeConstructor<Elab>): Boolean = other is ElabConstrL
    override fun split(other: CTypeConstructor<Elab>): List<Constraint<Elab>>? {
        return super.split(other)?.plus(LabelConstraint(label, (other as ElabConstrL).label))
    }
}

data class LabelConstraint(val a: Int, val b: Int) : Constraint<Elab> {
    override fun toString() = "L$a == L$b"
//    companion object {
//        fun <L : Language> simplify(constrs: List<Constraint<L>>): List<Constraint<L>> {
//            val (labels, irrelevant) = constrs.partition { it is LabelConstraint }
//            // Problem with making union find ds itself a constraint is when we reuse constraints for children we
//            // dont want to pass the same mutable ds. but then we also don't want to treat it differently than other
//            // constraints
//
//        }
//    }
}

/** Good style would be to hide this constructor somehow so it can only be instantiated by ElabV */
data class ElabConstrV(val v: Int, val instId: Int) : CVariable<Elab>, Substitutable {
    override fun toString() = "V${v}_$instId"
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
