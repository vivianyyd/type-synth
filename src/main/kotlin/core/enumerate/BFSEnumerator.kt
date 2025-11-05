package core.enumerate

import core.Candidate
import core.Language
import core.UnificationForCandidate
import query.Query
import java.util.*

class BFSEnumerator<L : Language>(
    val query: Query,
    seedCandidate: Candidate<L>,
    private val unification: UnificationForCandidate<L>,
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
                    !unification(
                        c, listOf(it)
                    ).ok()
                } else true)
                && unification(
                    c,
                    query.posExsBeforeSubexprs
                ).ok() // TODO shouldn't need this line, but we do
            ) ok.add(c)
        }

        do {
            curr = frontier.remove()
            val u = unification(curr, query.posExsBeforeSubexprs)
            // TODO We will often rediscover the same constraints even if two candidates are not identical...
            if (u.ok()) {
                if (curr.depth() > deepestSeen + 1) seen.clear()  // micro-opt

                // Need to prove: We will never miss a type just bc we didn't enum it in canonical form. If it exists, we will hit canonical form - completeness
                if (curr.full()) {
                    handleFull(curr)
                } else {
                    val exp = curr.bfsExpansions(u).filter {
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
