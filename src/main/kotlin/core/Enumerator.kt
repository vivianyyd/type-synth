package core

import query.App
import query.Name
import query.Query
import test.ConsTest
import util.lazyCartesianProduct
import java.util.*

class Enumerator<L : Language>(val query: Query, seedCandidate: Candidate<L>) {
    private val frontier = PriorityQueue<Candidate<L>>(compareBy({ it.depth }, { it.size }))
    private val seen = mutableSetOf<Candidate<L>>()
    private var deepestSeen = seedCandidate.depth + 1

    init {
        frontier.add(seedCandidate)
        seen.add(seedCandidate)
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
                if (curr.depth > deepestSeen + 1) seen.clear()  // micro-opt

                val exp = curr.expansions(constrs).filter {
                    eCandidateCount++
                    val unseen =
                        it !in seen  // we might be able to optimize this check away if there is a known exploration order
                    if (!unseen) eGeneratedDuplicate++
                    unseen
                }.toList()
                if (exp.isNotEmpty()) deepestSeen = curr.depth + 1  // micro-opt
                frontier.addAll(exp)
                seen.addAll(exp)
                if (curr.full() && curr.canonical()) ok.add(curr)  // Need to prove: We will never miss a type just bc we didn't enum it in canonical form. If it exists, we will hit canonical form - completeness
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
    }).map { Candidate(q.names, it) }
    // TODO one optimization: We can see if our candidate is a refinement of a previously rejected one
    //      if multiple things share structure, their antiunifier may be the conflict

    fun <L : Language> fromSeeds(seeds: Sequence<Candidate<L>>): Sequence<Candidate<L>> =
        seeds.flatMap {
            println("Seed: $it")
            Enumerator(q, it).enumerate(3)
        }

    val initSols = fromSeeds(inits)
    val elabSols = fromSeeds(initSols.map { compileInit(it) })

    val solslist = elabSols.toList()

    println(solslist.joinToString(prefix = "SOLUTIONS:\n", separator = "\n"))


    TODO(
        "In the next step, should we allow new labels to be introduced in expansions? " + "Will there ever be problems where a label type only occurs within other label types as a param?"
    )
}
