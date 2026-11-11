package dependencyanalysis

import org.junit.jupiter.api.Test
import testutil.oracleFromAssignment
import testutil.signedExamplesFromStrings
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class ParameterwiseDependencyAnalysisTest {
    private val types =
        "(Num (i));(true (b));(Li (l (i)));(Lb (l (b)));(cons (-> a (-> (l a) (l a))))"

    // Both positive examples: the prefix (cons true) of each negative example below is fine
    private val pos = arrayOf("(+ (cons Num Li))", "(+ (cons true Lb))")

    private fun analysis(vararg examples: String) =
        ParameterwiseDependencyAnalysis(
            signedExamplesFromStrings(examples.toList()),
            mapOf("Num" to 1, "true" to 1, "Li" to 1, "Lb" to 1, "cons" to 3),
            oracleFromAssignment(types),
        )

    @Test
    fun `a negative example whose argument fits the parameter elsewhere constrains it`() {
        // Li is accepted as cons's second argument, so (cons true Li) fails on the variable
        val dep = analysis(*pos, "(- (cons true Li))")
        assertTrue(dep.constrained["cons"]!![1])
    }

    @Test
    fun `a negative example whose argument fits the parameter nowhere does not constrain it`() {
        // Num is never cons's second argument: (cons true Num) may fail on the label alone
        val dep = analysis(*pos, "(- (cons true Num))")
        assertFalse(dep.constrained["cons"]!![1])
    }
}
