package dependencyanalysis

import query.Examples
import query.FlatApp
import util.Oracle
import util.PrefixBruteForce
import util.PrefixContainment
import util.eqClasses

data class ParameterNode(val f: String, val i: Int) {
    private var ctr = 0

    override fun toString(): String = "$f-$i"
}

/** Analyzes the parameters of [names], the names whose types aren't committed. */
class ParameterwiseDependencyAnalysis(
    private val examples: Examples,
    private val arities: Map<String, Int>,
    private val oracle: Oracle,
    resultDependence: Boolean = true,
    val names: Set<String> = examples.names.toSet(),
) {
    private val nodes =
        arities.filterKeys { it in names }.flatMap { (name, arity) -> (0 until arity).map { ParameterNode(name, it) } }

    fun nodes(name: String) = nodes.filter { it.f == name }

    val fixed = names.associateWith { Array(arities[it]!!) { false } }
    val constrained = names.associateWith { Array(arities[it]!!) { false } }

    /**
     * For each name, the parameters its result shares a variable with: those where two positive
     * examples that apply the name to all its parameters differ in the type of that argument only,
     * and the results' types differ. `(Pair.make Num Str)` and `(Pair.make true Str)` show that
     * `Pair.make`'s result depends on its first parameter.
     */
    val resultDependsOn = names.associateWith { Array(arities[it]!! - 1) { false } }

    override fun toString(): String =
        "Fixed: ${fixed.mapValues { it.value.contentToString() }}\tConstrained: ${constrained.mapValues { it.value.contentToString() }}" +
            "\tResult depends on: ${resultDependsOn.mapValues { it.value.contentToString() }}"

    init {
        names.forEach { name ->
            val arity = arities[name]!!

            val posExs = examples.flatPos(name)
            val negExs = examples.flatNeg(name)

            val prefixChecker: PrefixContainment = PrefixBruteForce(oracle)
            prefixChecker.addAll(posExs)

            val currFixed = fixed[name]!!
            val currConstrained = constrained[name]!!

            // Parameter k is constrained when a negative example fails at its kth argument, and
            // that argument's type is accepted at k in some positive example. Then the failure
            // can't be a label mismatch: the argument's labels fit the parameter. It must be
            // that the argument doesn't share a variable with earlier arguments the way the
            // parameter requires.
            // Requires: negative examples only fail on the LAST argument.
            negExs.forEach { neg ->
                val k = neg.args.size - 1
                if (k > 0 &&
                    arity > neg.args.size &&
                    !currConstrained[k] &&
                    prefixChecker.lookup(FlatApp(neg.name, neg.args.dropLast(1))) &&
                    posExs.any { k < it.args.size && oracle.flatEqual(it.args[k], neg.args[k]) }
                ) {
                    currConstrained[k] = true
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

            val applied = if (resultDependence) posExs.filter { it.args.size == arity - 1 } else emptyList()
            for (i in 0 until arity - 1) {
                // Examples alike in every argument but the ith
                val alikeButI =
                    applied.eqClasses { e1, e2 ->
                        e1.args.indices.all { j -> j == i || oracle.flatEqual(e1.args[j], e2.args[j]) }
                    }
                resultDependsOn[name]!![i] =
                    alikeButI.any { alike -> alike.any { !oracle.flatEqual(it, alike.first()) } }
            }

            //            for (i in 0 until arity) {
            //                for (j in 0 until arity) {
            //                    TODO("Check for observational equivalences and store for later
            // checking top-level variables consistent")
            //                }
            //            }
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
