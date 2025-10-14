package core

import query.App
import query.Name
import query.Query
import test.ConsTest
import util.clearCVC
import util.lazyCartesianProduct
import java.util.*

sealed interface Enumerator<L : Language> {
    fun enumerate(maxDepth: Int): List<Candidate<L>>
}

class BFSEnumerator<L : Language>(
    val query: Query,
    seedCandidate: Candidate<L>,
    private val mustPassNegatives: Boolean,
    private val minimizeSize: Boolean = false
) : Enumerator<L> {
    private val frontier = PriorityQueue<Candidate<L>>(compareBy({ it.depth() }, { it.size }))
    private val seen = mutableSetOf<Candidate<L>>()
    private var deepestSeen = seedCandidate.depth() + 1

    init {
        frontier.add(seedCandidate)
        seen.add(seedCandidate)
    }

    val ok = mutableListOf<Candidate<L>>() // TODO THIS WILL BE ONLY CONCRETE ONES

    var eCandidateCount = 0
    var eGeneratedDuplicate = 0
    var rejectedCandidate = 0

    override fun enumerate(maxDepth: Int): List<Candidate<L>> {
        var curr: Candidate<L>
        if (frontier.isEmpty()) return listOf()

        fun handleFull(c: Candidate<L>) {
            if (c.canonical() && (if (mustPassNegatives) query.negExamples.all {
                    Unification(
                        c, listOf(it)
                    ).get() == null
                } else true)
                && Unification(c, query.posExsBeforeSubexprs).get() != null  // TODO shouldn't need this line, but we do
            ) ok.add(c)
        }

        do {
            curr = frontier.remove()
            val constrs = Unification(curr, query.posExsBeforeSubexprs).get()
            // TODO We will often rediscover the same constraints even if two candidates are not identical...
            if (constrs != null) {
                if (curr.depth() > deepestSeen + 1) seen.clear()  // micro-opt

                // Need to prove: We will never miss a type just bc we didn't enum it in canonical form. If it exists, we will hit canonical form - completeness
                if (curr.full()) {
                    handleFull(curr)
                } else {
                    val exp = curr.bfsExpansions(constrs).filter {
                        eCandidateCount++
                        val unseen =
                            it !in seen  // we might be able to optimize this check away if there is a known exploration order
                        seen.add(it)  // TODO This is redundant
                        if (!unseen) eGeneratedDuplicate++
                        unseen// TODO && it.canonical()
                    }.toList()
                    if (exp.isNotEmpty()) deepestSeen = curr.depth() + 1  // micro-opt

                    val (full, hasHoles) = exp.partition { it.full() }
                    full.forEach { handleFull(it) }
                    frontier.addAll(hasHoles)
                    seen.addAll(exp)
                }
            } else rejectedCandidate++
        } while (curr.depth() <= maxDepth && frontier.isNotEmpty() && (if (minimizeSize && ok.isNotEmpty()) curr.size <= ok.first().size else true))

        println("Candidates enumerated: $eCandidateCount")
        println("Duplicate candidates: $eGeneratedDuplicate")
        println("Candidates rejected: $rejectedCandidate")

        println("Accepted candidates: ${ok.size}")
        println("Frontier: ${frontier.size}")
        return ok
    }
}

class DFSEnumerator<L : Language>(
    val query: Query,
    val seedCandidate: Candidate<L>,
    private val mustPassNegatives: Boolean,
    private val minimizeSize: Boolean = false
) : Enumerator<L> {
    private fun commitLeftmost(
        c: Candidate<L>,
        constrs: List<Constraint<L>>,
        recursionBound: Int
    ): Sequence<Candidate<L>> {
        val (changeInd, leftmostNode) = c.types.withIndex().firstOrNull { (_, it) -> it.holes() > 0 }
            ?: return sequenceOf(c)

        val optionsForLeftmost =
            leftmostNode.dfsLeftExpansions(constrs, leftmostNode.variableNames(), recursionBound).asSequence()

        return optionsForLeftmost.flatMap { (newLeftMost, commit) ->
            val newCandidate = Candidate(c.names, c.types.mapIndexed { i, p -> if (changeInd == i) newLeftMost else p })
            if (commit == null) {
                require(newCandidate == c)
                emptySequence() // this call made no changes, but we don't want to hit it again TODO verify this doesn't break completeness
            } else {
                val u = Unification(constrs)
                if (u.commitAndCheckValid(listOf(commit)))
                    commitLeftmost(newCandidate, u.get()!!, recursionBound)
                else emptySequence()
            }
        }
    }

    override fun enumerate(maxDepth: Int): List<Candidate<L>> {
        return commitLeftmost(
            seedCandidate,
            Unification(seedCandidate, query.posExsBeforeSubexprs).get() ?: return listOf(),
            maxDepth
        ).filter { c ->
            c.canonical() &&
                    Unification(
                        c,
                        query.posExsBeforeSubexprs
                    ).get() != null &&
                    (if (mustPassNegatives) query.negExamples.all {
                        Unification(
                            c, listOf(it)
                        ).get() == null
                    } else true)
        }.toList()
    }
}

val RERUN_CVC = true

fun main() {
    if (RERUN_CVC) clearCVC()

    val t = ConsTest
    val (query, oracle) = t.query to t.oracle

    val inits = lazyCartesianProduct(
        query.names.map { name ->
            InitHole().bfsExpansions().map { it.first }
                .filter { it is InitL || (it is NArrow && query.posExamples.any { it is App && it.fn is Name && it.fn.name == name }) }
        }).map { Candidate(query.names, it) }

    fun <L : Language> enum(seed: Candidate<L>, maxDepth: Int): List<Candidate<L>> =
        DFSEnumerator(query, seed, false).enumerate(maxDepth)

    fun <L : Language> fromSeeds(seeds: Sequence<Candidate<L>>, maxDepth: Int): Sequence<Candidate<L>> =
        seeds.flatMap { enum(it, maxDepth) }

    val initSols = fromSeeds(inits, 3)
    val elabSols = fromSeeds(initSols.map { compileInit(it) }, 3)

    val TIME = System.currentTimeMillis()
//        elabSols.filter {
//        val cons = it.types[it.names.indexOf("cons")]
//        cons is NArrow && cons.l is ElabV && cons.r is NArrow && cons.r.l is ElabL && cons.r.r is ElabL
//    }

    val concEnumerators = elabSols.mapNotNull {
        compileElab(it, query, oracle, RERUN_CVC)?.let {
            DFSEnumerator(query, it, mustPassNegatives = true, minimizeSize = true)
        }
    }.toList() // This needs to be a list so we don't keep calling it...

    println(concEnumerators.joinToString(separator = "\n") { "${it.seedCandidate}" })

    val sol = mutableListOf<Candidate<Concrete>>()
    for (i in 1..4) {
        println("Hello $i")
        val sols = concEnumerators.flatMap { it.enumerate(i) }.toList()
        if (sols.isNotEmpty()) {
            sol.addAll(sols)
            break
        }
    }

    println("FINAL SOLUTIONS:")
    println(sol.joinToString(separator = "\n"))

    println("TIME: ${System.currentTimeMillis() - TIME}")

    TODO("BRING BACK CEGIS LOOP")
//    println(solslist.joinToString(prefix = "SOLUTIONS:\n", separator = "\n"))
    TODO("Stop enumerating if we have all solutions of min size")
    TODO("Canonicalize wrt alpha equiv before storing in seen?")
    TODO(
        "In the next step, should we allow new labels to be introduced in expansions? " + "Will there ever be problems where a label type only occurs within other label types as a param?"
    )
}
