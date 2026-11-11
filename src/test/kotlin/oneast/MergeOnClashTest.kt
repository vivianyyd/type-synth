package oneast

import testutil.loadQueryFromFile
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

/**
 * label-merge.sexp, with its helpers in a first round: p's label is fixed only through k q p, by
 * q's parameter, which m q fixes. Its outline gives p a new label, which clashes with lv's while
 * concretizing q, so the search merges the two labels (see [Search.mergedOutlines]).
 */
class MergeOnClashTest {
    private val helpers = listOf("one", "lv", "nv", "inc", "mk", "k", "m", "n")

    /** With no parameters past the solver's bounds, so M keeps its one parameter. */
    private fun assertSolvedAfterHelpers(vararg rounds: List<String>) {
        val query = loadQueryFromFile("label-merge")
        val config =
            Configuration(
                sizeBound = 20,
                depthBound = 4,
                scheduleInfo = CustomSchedule(listOf(helpers) + rounds.toList()),
                numSols = Solutions.NumSolutions(1),
                extraArities = 0,
            )
        val solutions = run(query, query.oracle, config)
        assertEquals(1, solutions.size)
        assertTrue(solutions.single().equivalentTo(query.oracle.truth), "${solutions.single()}")
    }

    @Test
    fun `p and q in one round`() = assertSolvedAfterHelpers(listOf("p", "q"))

    @Test
    fun `p, then q`() = assertSolvedAfterHelpers(listOf("p"), listOf("q"))
}
