package util

import org.junit.jupiter.api.Test
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource
import testutil.loadQueryFromFile
import testutil.oracleFromAssignment
import testutil.signedExamplesFromStrings
import testutil.unsignedExample
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class ObservationalEquivalenceOracleTest {
    private fun oracle(types: String, vararg examples: String) =
        ObservationalEquivalenceOracle(
            signedExamplesFromStrings(examples.toList()), oracleFromAssignment(types)
        )

    private fun ObservationalEquivalenceOracle.equal(a: String, b: String) =
        equal(unsignedExample(a), unsignedExample(b))

    @Test
    fun `swapped-in expression must not fail earlier in a minimal negative example`() {
        // f (j h) fails like f (g h) does, but already at j h, which g h doesn't
        val o =
            oracle(
                "(f (-> (b) (i)));(g (-> (i) (i)));(k (-> (i) (i)));(j (-> (b) (i)));(h (i))",
                "(- (f (g h)))",
                "(- (f (k h)))",
                "(- (f (j h)))",
            )
        assertFalse(o.equal("g", "j"))
        assertTrue(o.equal("g", "k"))
    }

    @Test
    fun `occurrences are swapped individually`() {
        // Swapping both x's for y gives eq y y, which is fine; swapping one gives eq y x, which isn't
        val o =
            oracle(
                "(eq (-> a (-> a (b))));(x (i));(y (b));(z (i))",
                "(+ (eq x x))",
                "(+ (eq y y))",
                "(+ (eq z z))",
            )
        assertFalse(o.equal("x", "y"))
        assertTrue(o.equal("x", "z"))
    }

    @Test
    fun `invalid expressions are not equal to anything`() {
        val o = oracle("(x (i));(y (b))", "(+ x)", "(+ y)", "(- (x y))")
        assertFalse(o.equal("(x y)", "(x y)"))
        assertTrue(o.equal("x", "x"))
    }

    @Test
    fun `subexpressions are compared`() {
        val o = loadQueryFromFile("cons").let { ObservationalEquivalenceOracle(it.examples, it.oracle) }
        assertTrue(o.equal("Li", "(cons Num Li)"))
        assertTrue(o.equal("(cons Num)", "(cons Num)"))
        assertFalse(o.equal("Num", "true"))
        assertFalse(o.equal("Li", "LLi"))
        assertFalse(o.equal("(cons Num)", "(cons Li)"))
    }

    @Test
    fun `dummies number equivalence classes`() {
        val o = loadQueryFromFile("cons").let { ObservationalEquivalenceOracle(it.examples, it.oracle) }
        val li = o.dummy(unsignedExample("Li"))
        assertEquals(li, o.dummy(unsignedExample("(cons Num Li)")))
        assertTrue(li != o.dummy(unsignedExample("LLi")))
    }

    /** With a ground truth that comes from types, expressions of the same type can't be told apart. */
    @ParameterizedTest
    @MethodSource("oneast.SexpTests#testNames")
    fun `expressions of the same type are equal`(name: String) {
        val query = loadQueryFromFile(name)
        val types = query.oracle
        val o = ObservationalEquivalenceOracle(query.examples, types)
        val exprs = query.examples.posWithSubexprs
        for (a in exprs) for (b in exprs) {
            if (types.equal(a, b)) assertTrue(o.equal(a, b), "$a and $b have the same type")
        }
    }
}
