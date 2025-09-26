package core

import query.App
import query.Name
import query.Query
import test.ConsTest
import util.Counter
import util.UnionFind
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
            val constrs = Unification(curr, query.posExsBeforeSubexprs).get()
            // TODO We will often rediscover the same constraints even if two candidates are not identical...
            //      also, refinements of simpler candidates inherit their constraints, but we don't keep that state
            if (constrs != null) {
                println(curr)
                val exp = curr.expansions(constrs).filter {
                    eCandidateCount++
                    val unseen = it !in seen
                    if (!unseen) eGeneratedDuplicate++
                    unseen
                }.toList()

                frontier.addAll(exp)
                seen.addAll(exp)
                if (exp.isEmpty()) ok.add(curr)
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
        InitHole.expansions().map { it.first }
            .filter { it is InitL || (it is NArrow && q.posExamples.any { it is App && it.fn is Name && it.fn.name == name }) }
    })

    /*
    expansions NArrow is cartesian prod of params expansions:

    Candidates enumerated: 47
    Duplicate candidates: 11
    Candidates rejected: 11
    Accepted candidates: 11
    Frontier: 11
    Accepted candidates: [0: L, LLi: L, Li: L, []b: L, cons: V -> V, tr: L, 0: L, LLi: L, Li: L, []b: L, cons: L -> V, tr: L, 0: L, LLi: L, Li: L, []b: L, cons: V -> V -> V, tr: L, 0: L, LLi: L, Li: L, []b: L, cons: V -> V -> L, tr: L, 0: L, LLi: L, Li: L, []b: L, cons: V -> L -> V, tr: L, 0: L, LLi: L, Li: L, []b: L, cons: V -> L -> L, tr: L, 0: L, LLi: L, Li: L, []b: L, cons: L -> L -> L, tr: L, 0: L, LLi: L, Li: L, []b: L, cons: L -> V -> V, tr: L, 0: L, LLi: L, Li: L, []b: L, cons: L -> V -> L, tr: L, 0: L, LLi: L, Li: L, []b: L, cons: L -> L -> V, tr: L, 0: L, LLi: L, Li: L, []b: L, cons: V -> V -> L -> L, tr: L]

     */

    val answers = inits.flatMap {
        println("Seed: $it")
        val e = Enumerator(ConsTest.query, Candidate(q.names, it))
        e.enumerate(3)
    }
    println(answers.toList().joinToString(separator = "\n"))


    // TODO: Now that we have a sequence of candidate Inits, translate them into seeds for the next round, then
    //   do enum on those. When we compile Init to Elab, that's were we can figure out what vars in scope

    TODO(
        "In the next step, should we allow new labels to be introduced in expansions? " + "Will there ever be problems where a label type only occurs within other label types as a param?"
    )
}

object Init : Language

object InitV : Leaf<Init> {
    override fun toString() = "V"
    override fun instantiate(i: Counter, insts: Int): ConstraintType<Init> = InitConstrV
}

object InitL : Leaf<Init> {
    override fun toString() = "L"
    override fun instantiate(i: Counter, insts: Int): ConstraintType<Init> = InitConstrL
}

object InitHole : Hole<Init>() {
    override fun expansions(): List<Pair<SearchNode<Init>, Commitment<Init>>> =
        listOf(NArrow(InitHole, InitHole), InitV, InitL).map { it to (this to it) }
}

object InitConstrV : CVariable<Init>

object InitConstrL : CTypeConstructor<Init>(mutableListOf()) {
    override fun match(other: CTypeConstructor<Init>): Boolean = other is InitConstrL
}

object Elab : Language

data class ElabV(val v: Int) : Leaf<Elab> {
    override fun toString() = "V$v"
    override fun instantiate(i: Counter, insts: Int): ConstraintType<Elab> = ElabConstrV(v, insts)
}

data class ElabL(val label: Int) : Leaf<Elab> {
    override fun toString() = "L$label"
    override fun instantiate(i: Counter, insts: Int): ConstraintType<Elab> = ElabConstrL()
}

data class ElabVarHole(val vars: List<Int>) : Hole<Elab>() {
    override fun toString() = "V_"
    override fun expansions(): List<Pair<SearchNode<Elab>, Commitment<Elab>>> =
        vars.map { ElabV(it) }.map { it to (this to it) }
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
 *  For both options, the reset can be done in a translateCandidate() fn so it's not horrible either way. UF faster
 * */
//data class ElabLabHole(val labels: List<Int>) : Hole<Elab>() {
//    companion object {
//        var nLabels = 0
//    }
//
//    init {
//        nLabels++
//    }
//
//    override fun toString() = "L_"
//    override fun expansions(): List<SearchNode<Elab>> = labels.map { ElabL(it) }
//}

/** Good style would be to hide this constructor somehow so it can only be instantiated by ElabV */
data class ElabConstrV(val v: Int, val instId: Int) : CVariable<Elab>, Substitutable {
    override fun toString() = "V${v}_$instId"
}

data class ElabConstrL private constructor(val label: Int) : CTypeConstructor<Elab>(mutableListOf()) {
    constructor() : this(classes.add())

    companion object {
        var classes = UnionFind()

        fun reset() {
            classes = UnionFind()
        }
    }

    override fun match(other: CTypeConstructor<Elab>): Boolean = other is ElabConstrL
    override fun split(other: CTypeConstructor<Elab>): List<Constraint<Elab>>? {
        val sup = super.split(other)
        if (sup != null) classes.union(label, (other as ElabConstrL).label)
        return sup
    }
}
