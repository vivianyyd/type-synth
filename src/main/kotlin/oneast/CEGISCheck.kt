package oneast

import query.Example
import query.Examples
import util.BloomFilter
import util.RandomExampleGenerator

class CEGISCheck(
    private val initExamples: Examples,
    private val candidate: SearchState,
    private val valid: (Example) -> Boolean,
    private val check: (SearchState, Example) -> Boolean,
) {
    private val generator = RandomExampleGenerator(initExamples.names)
    private val exampleDepthBound = candidate.fnArities().values.max()
    private var posCtr = 0
    private val bf = BloomFilter<Example>(200)

    init {
        initExamples.posWithSubexprs.forEach { bf.add(it) }
    }

    private fun justCheckOGExamples(): Pair<Example, Boolean>? {
        for (p in initExamples.posNoSubexprs) {
            if (!check(candidate, p)) return p to true
        }
        for (n in initExamples.neg) {
            if (check(candidate, n)) return n to true
        }
        return null
    }

    fun counterexample(): Pair<Example, Boolean>? {
        return justCheckOGExamples()
        return null // TODO remove me
        while (posCtr < 10) {
            val next = generator.get(exampleDepthBound)
            // TODO Check if it's more efficient to bloom filter it, or check truth value first?
            val truthValue = valid(next)
            if (check(candidate, next) != truthValue) {
                return next to truthValue
            }
            if (truthValue && !bf.mightContain(next)) {
                println("Found posex $next")
                posCtr++
                bf.add(next)
            }
            //            if (!bf.mightContain(next)) {
            //                val truthValue = valid(next)
            //                if (check(candidate, next) != truthValue) {
            //                    return next to truthValue
            //                }
            //                if (truthValue) {
            //                    println("Found posex $next")
            //                    posCtr++
            //                    bf.add(next)
            //                }
            //            }
        }
        return null
    }
}
