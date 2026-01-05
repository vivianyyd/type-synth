package dependencyanalysis

import query.FlatApp
import query.Query
import util.Oracle
import util.PrefixBruteForce
import util.PrefixContainment
import util.equivalenceClasses

class EquivalenceRelation(private val oracle: Oracle) {
    private val representatives = mutableListOf<FlatApp>()

    fun addExample(arg: FlatApp) {
        if (!match(arg)) representatives.add(arg)
    }

    fun match(arg: FlatApp) = representatives.any {
        oracle.flatEqual(it, arg)
    }
}

class ParameterwiseDependencyAnalysis(
    private val query: Query,
    private val arities: Map<String, Int>,
    private val oracle: Oracle
) {
    private val nodes =
        arities.flatMap { (name, arity) -> (0 until arity).map { ParameterNode(name, it) } }

    fun nodes(name: String) = nodes.filter { it.f == name }

    val fresh = query.names.associateWith { Array(arities[it]!!) { false } }
    val constrained = query.names.associateWith { Array(arities[it]!!) { false } }

    init {
        query.names.forEach { name ->
            val posExs = query.flatPosNoSubexprs(name)
            val negExs = query.flatNeg(name)

            val prefixChecker: PrefixContainment = PrefixBruteForce(oracle)
            prefixChecker.addAll(posExs)

            negExs.forEach { neg ->
                // requires: negative examples only fail on the LAST argument
                if (prefixChecker.lookup(FlatApp(neg.name, neg.args.dropLast(1))))
                    TODO("Add a constraint in the appropriate place")
            }

            TODO("Fresh variable analysis")
        }
    }

    /**
     * In each equivalence class, the type of the function that the arg at [argIndex] is applied
     * to is the same
     */
    fun groupExsByTypeBeforeArg(argIndex: Int, exs: Collection<FlatApp>) =
    // TODO A weaker version of this is to check that all the arguments themselves are obs
    //      equivalent. Tradeoffs? Use that if the oracle doesn't work for arbitrary
    //      subexpressions.. But it should.
    //      e1.args.subList(0, argIndex).zip(e2.args.subList(0, argIndex)).all { (a1, a2) ->
        //          oracle.flatEqual(a1, a2) }
        equivalenceClasses(exs) { e1, e2 ->
            oracle.flatEqual(
                FlatApp(e1.name, e1.args.subList(0, argIndex)),
                FlatApp(e2.name, e2.args.subList(0, argIndex))
            )
        }
}

/*
       fun exsInvolving(paramIndex: Int): List<FlatApp> =
           if (paramIndex < nodes.size - 1)
               posExs.filter { it.args.size > paramIndex && it.args.size < nodes.size }
           else posExs.filter { it.args.size == paramIndex }

       /** Requires: i is in bounds for ex. */
       fun arg(ex: FlatApp, paramIndex: Int) =
           if (paramIndex == ex.args.size) ex else ex.args[paramIndex]

       fun witnesses(paramIndex: Int): List<FlatApp> =
           exsInvolving(paramIndex).map { arg(it, paramIndex) }
*/
