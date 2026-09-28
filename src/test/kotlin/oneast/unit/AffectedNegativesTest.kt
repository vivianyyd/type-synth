package oneast.unit

import oneast.*
import oneast.searchstrategies.DFSEnumerator
import oneast.searchstrategies.SearchStrategy
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.ValueSource
import query.Examples
import testutil.loadQueryFromFile
import util.Logger
import util.io.cvc.clearCVC
import kotlin.test.assertEquals

/**
 * Re-checking only the negatives a fill can affect is a shortcut, so the search must see exactly the
 * same candidates, and prune exactly as often, as when it re-checks all of them.
 */
class AffectedNegativesTest {
    /** Records every seed an enumerator is given and every candidate it returns, in order. */
    private class Recording(
        examples: Examples,
        private val inner: SearchStrategy,
        private val seen: MutableList<String>
    ) : SearchStrategy(examples) {
        override fun candidates(c: SearchState): Sequence<SearchState> {
            seen.add("seed $c")
            return inner.candidates(c).onEach { seen.add(it.toString()) }
        }
    }

    private fun search(name: String, onlyAffected: Boolean): Pair<List<String>, Int> {
        // Solver files are named by state id, which restarts every run, so a file left over from an
        // earlier run can be read as this run's result.
        clearCVC()
        val query = loadQueryFromFile(name)
        val seen = mutableListOf<String>()
        val configuration =
            Configuration(
                name = name,
                searchStrategy = { examples, emitBlanks, emitConstructors, sizeBound, depthBound, logger ->
                    Recording(
                        examples,
                        DFSEnumerator(
                            examples,
                            emitBlanks,
                            emitConstructors,
                            sizeBound,
                            depthBound,
                            logger,
                            checkOnlyAffectedNegatives = onlyAffected
                        ),
                        seen
                    )
                },
                sizeBound = 20,
                depthBound = 4,
                scheduleInfo = SingleRound,
                numSols = Solutions.NumSolutions(1)
            )
        val logger = Logger(configuration, logToFile = false, verbosity = 5)
        val solutions = run(query, query.oracle, configuration, logger)
        seen.add("solutions $solutions")
        return seen to logger.countOf("Pruned by negative examples")
    }

    @ParameterizedTest
    @ValueSource(strings = ["cons", "polymorphic-nil", "dictput", "dictchain", "polymorphic-dictchain"])
    fun `checking only affected negatives changes nothing`(name: String) {
        val (allCandidates, allPruned) = search(name, onlyAffected = false)
        val (affectedCandidates, affectedPruned) = search(name, onlyAffected = true)
        assertEquals(allCandidates, affectedCandidates)
        assertEquals(allPruned, affectedPruned)
    }
}
