package dependencyanalysis

import query.FlatApp
import query.Query
import util.Oracle
import util.PrefixBruteForce
import util.PrefixContainment
import util.eqClasses

class ParameterwiseDependencyAnalysis(
    private val query: Query,
    private val arities: Map<String, Int>,
    private val oracle: Oracle
) {
    private val nodes =
        arities.flatMap { (name, arity) -> (0 until arity).map { ParameterNode(name, it) } }

    fun nodes(name: String) = nodes.filter { it.f == name }

    val fixed = query.names.associateWith { Array(arities[it]!!) { false } }
    val constrained = query.names.associateWith { Array(arities[it]!!) { false } }

    init {
        query.names.forEach { name ->
            val arity = arities[name]!!

            val posExs = query.flatPosNoSubexprs(name)
            val negExs = query.flatNeg(name)

            val prefixChecker: PrefixContainment = PrefixBruteForce(oracle)
            prefixChecker.addAll(posExs)

            val currFixed = fixed[name]!!
            val currConstrained = constrained[name]!!

            negExs.forEach { neg ->
                // requires: negative examples only fail on the LAST argument
                if (neg.args.size > 1 &&
                    !currConstrained[neg.args.size - 1] &&
                    prefixChecker.lookup(FlatApp(neg.name, neg.args.dropLast(1)))
                ) {
                    currConstrained[neg.args.size - 1] = true
                }
            }

            // we can never eliminate the case where the output is always [], so only try to compute
            // fixed input parameters
            for (i in 1 until arity - 1) {
                // we can't enforce with hm types if an input param is only allowed to be nil,
                // so assume that if the input parameter is a l[a] with fresh a, we see variation in
                // what a is bound to.

                // Group relevant positive examples by their type before arguments in this position
                // are applied
                val witnessPrefixes =
                    posExs
                        .filter { i < it.args.size }
                        .eqClasses { e1, e2 ->
                            // TODO A weaker version of this is to check that all the arguments
                            //   themselves are obs equivalent. Tradeoffs? Use that if the oracle
                            //   doesn't work for arbitrary subexpressions.. But it should.
                            //      e1.args.subList(0, argIndex).zip(
                            //          e2.args.subList(0, argIndex)).all {(a1, a2) ->
                            //              oracle.flatEqual(a1, a2) }
                            oracle.flatEqual(
                                FlatApp(e1.name, e1.args.subList(0, i)),
                                FlatApp(e2.name, e2.args.subList(0, i))
                            )
                        }

                if (witnessPrefixes.all { exsSameTypeBeforeI ->
                        exsSameTypeBeforeI.all {
                            // for all examples with the same type prefix, the ith argument is always
                            // the same type
                            oracle.flatEqual(it.args[i], exsSameTypeBeforeI.first().args[i])
                        }
                    }) {
                    currFixed[i] = true
                }
            }

            for (i in 0 until arity) {
                for (j in 0 until arity) {
                    TODO("Check for observational equivalence")
                }
            }
        }
    }

    fun mayHaveFresh(p: ParameterNode): Boolean = !fixed[p.f]!![p.i]
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
