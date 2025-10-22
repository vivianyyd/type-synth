package core

import query.App
import query.Name
import query.Query
import query.parseContextAndExamples
import test.*
import util.clearCVC
import util.lazyCartesianProduct
import util.readExamples
import java.io.File
import java.io.PrintStream
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
        fun check(c: Candidate<L>) =
            Unification(c, query.posExsBeforeSubexprs).get() != null &&
                    (if (mustPassNegatives)
                        query.negExamples.all { Unification(c, listOf(it)).get() == null }
                    else true)

        return commitLeftmost(
            seedCandidate, Unification(seedCandidate, query.posExsBeforeSubexprs).get() ?: return listOf(), maxDepth
        ).filter { c -> c.canonical() && check(c) }.toList()
    }
}

class DFSPriorityEnumerator<L : Language>(
    val query: Query,
    val seedCandidate: Candidate<L>,
    private val mustPassNegatives: Boolean,
    private val minimizeSize: Boolean = false
) : Enumerator<L> {
    private fun commitPriority(
        c: Candidate<L>,
        constrs: List<Constraint<L>>,
        recursionBound: Int
    ): Sequence<Candidate<L>> {
        println("Exploring $c")
        if (
            c.toString()
                .contains("chain: L1[V1, V2] -> L1[V2, V3] -> L1[V1, V3], dbb: L1[L0[], L0[]], dbi: L1[L0[], L8[]], dib: L1[L8[], L0[]], dii: L1[L8[], L8[]], i: L8[], put: L1[V0, V1] -> V0 -> V1 -> L1[V0, V1")
        ) {
            println("I have $c")
            println(Unification(c, query.posExsBeforeSubexprs).get())
            println(Unification(c, query.negExamples.toList()).get())
            TODO()
        }

        val (changeInd, prioritized) = c.types.withIndex().maxByOrNull { (_, it) -> it.priority() }
            ?: return sequenceOf(c)
        if (prioritized.priority() == 0) return sequenceOf(c)
//        println("Prioritized hole: $prioritized")

        val optionsForPrioritized =
            prioritized.dfsPriorityExpansions(constrs, prioritized.variableNames(), recursionBound).asSequence()

        return optionsForPrioritized.flatMap { (newType, commit) ->
            val newCandidate = Candidate(c.names, c.types.mapIndexed { i, p -> if (changeInd == i) newType else p })
            if (commit == null) {
                require(newCandidate == c)
                emptySequence() // this call made no changes, but we don't want to hit it again TODO verify this doesn't break completeness
            } else {
                val u = Unification(constrs)
                if (u.commitAndCheckValid(listOf(commit)))
                    commitPriority(newCandidate, u.get()!!, recursionBound)
                else emptySequence()
            }
        }
    }

    override fun enumerate(maxDepth: Int): List<Candidate<L>> {
        fun check(c: Candidate<L>) =
            Unification(c, query.posExsBeforeSubexprs).get() != null &&
                    (if (mustPassNegatives)
                        query.negExamples.all { Unification(c, listOf(it)).get() == null }
                    else true)

        return commitPriority(
            seedCandidate, Unification(seedCandidate, query.posExsBeforeSubexprs).get() ?: return listOf(), maxDepth
        ).filter { c -> c.canonical() && check(c) }.toList()
    }
}

data class PortNode<L : Language>(val options: List<MutableList<PortNode<L>>>) {

}

class ProductEnumerator<L : Language>(
    val query: Query,
    val seedCandidate: Candidate<L>,
    private val mustPassNegatives: Boolean,
    val depth: (Candidate<L>) -> Int,
    private val minimizeSize: Boolean = false
) : Enumerator<L> {
    private val state = mutableListOf<SearchNode<L>>()

    init {
        TODO()
    }

    fun step(): List<List<SearchNode<L>>> {
        val sols = mutableListOf<List<SearchNode<L>>>()
        state.forEach {
            /*
            If it's an arrow,
                if its depth is greater than both child's depth,
                    enumerate normally (call enumerate on this node directly; default recursion bound is fine)
                Otherwise,
                    call step param on left child (calls normal enumerate with default recursion bound)
                    recurse this special casing on right child
             */
        }
        TODO()
    }

    override fun enumerate(maxDepth: Int): List<Candidate<L>> {
        TODO()


//        // 1. Get constraints for each function from Unification
//        val constrs = Unification(seedCandidate, query.posExsBeforeSubexprs).get() ?: return listOf()
//        // 2. For each function, enumerate possible building blocks (expansions)
//        val optionsPerFunction = seedCandidate.types.mapIndexed { i, node ->
//            node.expansions(constrs, node.variableNames(), maxDepth).map { it.first }
//        }
//        // 3. Generate all combinations (cartesian product) of building blocks
//        val candidates = lazyCartesianProduct(optionsPerFunction).map { Candidate(seedCandidate.names, it) }
//        // 4. Filter candidates by constraints and examples
//        return candidates.filter { c ->
//            c.canonical() &&
//                    Unification(c, query.posExsBeforeSubexprs).get() != null &&
//                    (if (mustPassNegatives) query.negExamples.all {
//                        Unification(c, listOf(it)).get() == null
//                    } else true)
//        }.toList()
    }
}

val RERUN_CVC = false

fun main() {
    if (RERUN_CVC) clearCVC()

    val logFile = File("app.log")
    System.setOut(PrintStream(logFile.outputStream(), true))
    System.setErr(PrintStream(logFile.outputStream(), true))

    val smallTests = listOf(IdTest, ConsTest, HOFTest, DictTest, WeirdTest)
    val t = ConsTest
    val testFromFile = parseContextAndExamples(readExamples("dictchain-smaller"))

//    val (query, oracle) = t.query to t.oracle
    val (query, oracle) = testFromFile

    val inits = lazyCartesianProduct(
        query.names.map { name ->
            InitHole().bfsExpansions().map { it.first }
                .filter { it is InitL || (it is NArrow && query.posExamples.any { it is App && it.fn is Name && it.fn.name == name }) }
        }).map { Candidate(query.names, it) }

    fun <L : Language> enum(seed: Candidate<L>, maxDepth: Int): List<Candidate<L>> =
        DFSEnumerator(query, seed, false).enumerate(maxDepth)

    fun <L : Language> fromSeeds(seeds: Sequence<Candidate<L>>, maxDepth: Int): Sequence<Candidate<L>> =
        seeds.flatMap { enum(it, maxDepth) }

    val TIME = System.currentTimeMillis()

    val initSols = fromSeeds(inits, 4)
    var elabSols = fromSeeds(initSols.map { compileInit(it) }, 4)


//        elabSols = elabSols.filter {
//        val cons = it.types[it.names.indexOf("cons")]
//        cons is NArrow && cons.l is ElabV && cons.r is NArrow && cons.r.l is ElabL && cons.r.r is ElabL
//    }

    // TODO deleteme
//    elabSols = elabSols.filter {
//        val put = it.types[it.names.indexOf("put")]
//        put is NArrow && put.l is ElabL && put.r is NArrow && put.r.l is ElabV && put.r.r is NArrow && put.r.r.l is ElabV && put.r.r.r is ElabL
//    }

    val concEnumerators = elabSols.mapNotNull {
        compileElab(it, query, oracle, RERUN_CVC)?.let {
            DFSPriorityEnumerator(query, it, mustPassNegatives = true, minimizeSize = true)
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
