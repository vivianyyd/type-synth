package oneast

import query.Example
import query.Examples
import util.BloomFilter

class CEGISCheck(
    initExamples: Examples,
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

    fun counterexample(): Pair<Example, Boolean>? {
        while (posCtr < 100) {
            val next = generator.get(exampleDepthBound)
            if (!bf.mightContain(next)) {
                val truthValue = valid(next)
                if (check(candidate, next) != truthValue) {
                    return next to truthValue
                }
                if (truthValue) {
                    posCtr++
                    bf.add(next)
                }
            }
        }
        return null
    }
}
