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
    val frontier = PriorityQueue<Candidate<L>>(compareBy { it.size })
    val seen = mutableSetOf<Candidate<L>>()

    init {
        frontier.add(seedCandidate)
    }

    val ok = mutableListOf<Candidate<L>>() // TODO THIS WILL BE ONLY CONCRETE ONES

    fun enumerate(maxDepth: Int): List<Candidate<L>> {
        var curr: Candidate<L>
        do {
            curr = frontier.remove()
            val constrs = Unification(curr, query.posExsBeforeSubexprs).get()
            // TODO We will often rediscover the same constraints even if two candidates are not identical...
            //      also, refinements of simpler candidates inherit their constraints, but we don't keep that state
            if (constrs != null) {
                val exp = curr.expansions(constrs).filter { it !in seen }
                frontier.addAll(exp)
                seen.addAll(exp)
                if (exp.isEmpty()) ok.add(curr)
            } else println("failed: $curr")
        } while (curr.depth <= maxDepth && frontier.isNotEmpty())


        println("frontier: $frontier")
        return ok
    }
}

fun main() {
    val q = ConsTest.query
    val inits = lazyCartesianProduct(q.names.map { name ->
        InitHole.expansions()
            .filter { it is InitL || (it is NArrow && q.posExamples.any { it is App && it.fn is Name && it.fn.name == name }) }
    })

    val answers = inits.flatMap {
        val e = Enumerator(ConsTest.query, Candidate(q.names, it))
        e.enumerate(3)
    }
    println(answers.toList().joinToString(separator = "\n"))
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

object InitHole : Hole<Init>(listOf()) {  // TODO This constructor call is dubious
    override fun expansions(): List<SearchNode<Init>> = listOf(NArrow(InitHole, InitHole), InitV, InitL)
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

// TODO Does it make sense for holes to be objects?
object ElabHole : Hole<Elab>(listOf()) {  // TODO This constructor call is dubious
    override fun expansions(): List<SearchNode<Elab>> {
        TODO("Not yet implemented. I think we don't even do any expansions at this step")
        TODO(
            "In the next step, should we allow new labels to be introduced in expansions? " +
                    "Will there ever be problems where a label type only occurs within other label types as a param?"
        )
    }
}

/** Good style would be to hide this constructor somehow so it can only be instantiated by ElabV */
data class ElabConstrV(val v: Int, val instId: Int) : CVariable<Elab>, Substitutable
data class ElabConstrL private constructor(val label: Int) : CTypeConstructor<Elab>(mutableListOf()) {
    constructor() : this(classes.add())

    companion object {
        val classes = UnionFind()
    }

    override fun match(other: CTypeConstructor<Elab>): Boolean = other is ElabConstrL
    override fun split(other: CTypeConstructor<Elab>): List<Constraint<Elab>>? {
        val sup = super.split(other)
        if (sup != null) classes.union(label, (other as ElabConstrL).label)
        return sup
    }
}
