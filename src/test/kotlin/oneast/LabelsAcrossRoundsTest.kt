package oneast

import query.Query
import testutil.oracleFromAssignment
import testutil.signedExamplesFromStrings
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotEquals
import kotlin.test.assertNotNull

/**
 * Round 0 has `zero`, `one` and `true`, which no example of round 0 relates, so it gives each a
 * label of its own. The examples of round 1 need `zero` and `one` to share one, so the two rounds
 * have to be searched again as one.
 */
class LabelsAcrossRoundsTest {
    /** A solution for round 1 being [fn], of type [type]. */
    private fun solve(fn: String, type: String, examples: List<String>): SearchState? {
        val types = "(zero (n));(one (n));(true (b));($fn $type)"
        val query = Query(signedExamplesFromStrings(examples), oracleFromAssignment(types))
        val config =
            Configuration(
                sizeBound = 20,
                depthBound = 4,
                scheduleInfo = CustomSchedule(listOf(listOf("zero", "one", "true"), listOf(fn))),
                numSols = Solutions.NumSolutions(1),
            )
        return run(query, query.oracle, config).firstOrNull()
    }

    private fun assertZeroAndOneShareALabel(solution: SearchState?) {
        assertNotNull(solution)
        assertEquals(solution.typeOf("zero"), solution.typeOf("one"))
        assertNotEquals(solution.typeOf("zero"), solution.typeOf("true"))
    }

    /** Positive unification fails when `compare`'s two arguments are one variable. */
    @Test
    fun `a clash when unifying`() =
        assertZeroAndOneShareALabel(
            solve(
                "compare",
                "(-> a (-> a (b)))",
                listOf("(+ true)", "(+ (compare zero one))", "(+ (compare one zero))", "(- (compare zero true))")
            )
        )

    /**
     * `isZero`'s argument is unified with both labels, so it can only be a variable, which accepts
     * the negative example. Nothing fails to unify.
     */
    @Test
    fun `a clash in a hole`() =
        assertZeroAndOneShareALabel(
            solve(
                "isZero",
                "(-> (n) (b))",
                listOf("(+ true)", "(+ (isZero zero))", "(+ (isZero one))", "(- (isZero true))")
            )
        )
}
