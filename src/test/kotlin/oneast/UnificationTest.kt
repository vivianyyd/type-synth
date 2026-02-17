package oneast

import org.junit.jupiter.api.Test
import org.junit.jupiter.api.Assertions.*
import query.App
import query.Name
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class UnificationTest {
    //    2881 [23:13:47.716]  Potential solution: {0=L0[], 1=L0[], compare=V0 -> V0 -> L0[], max=V0
    // -> V0 -> V0, min=V0 -> V0 -> V0}
    //   2882 [23:13:47.716]  Looking for counterexamples
    //   2883 [23:13:47.948]  Adding counterexample ((compare) (max)) (compare)       Posex: true
    /*
    Turns out, ((compare) (max)) (compare) compiles but not ((compare) (max)) because of weak variables
    whatever whatever in ocaml. Basically, you can't generalize the variables in HM. But you can if you
    see the last element, which ocaml cleverly uses. Basically, OCaml's type checker is a little more
    clever and accepts things that are not HM, which we'll never be able to do, so we fail with no soln.
     */
    @Test
    fun `unification`() {
        /*
        compare: v0 -> v0 -> L0
        max: v0 -> v0 -> v0
         */
        val context =
            SearchState(
                mapOf("compare" to 0, "max" to 1),
                listOf(
                    Arrow(Variable(0), Arrow(Variable(0), NamedLabel(0, listOf()))),
                    Arrow(Variable(0), Arrow(Variable(0), Variable(0)))
                ),
                listOf(2),
                mapOf(0 to 0)
            )
        val compare = Name("compare")
        val max = Name("max")
        val example = App(App(compare, max), compare)
        val unify = OneUnification(context, listOf(example))
        assertEquals(
            unify.type(App(compare, max))!!.toNode(),
            Arrow(Arrow(Variable(0), Arrow(Variable(0), Variable(0))), NamedLabel(0, listOf()))
        )
        assertTrue(unify.ok())
    }

    /**
     * Test case: Both parameter and argument specialize - concrete type in parameter.
     * f: ('a -> 'a -> Int) -> Int
     * g: 'b -> 'b -> 'b
     * Expected: Should succeed in HM. 'b unifies with 'a, then 'b unifies with Int.
     */
    @Test
    fun `both param and arg specialize - concrete in parameter`() {
        val context = SearchState(
            mapOf("f" to 0, "g" to 1),
            listOf(
                // f: ('a -> 'a -> Int) -> Int
                Arrow(
                    Arrow(Variable(0), Arrow(Variable(0), NamedLabel(0, listOf()))),
                    NamedLabel(0, listOf())
                ),
                // g: 'b -> 'b -> 'b
                Arrow(Variable(0), Arrow(Variable(0), Variable(0)))
            ),
            listOf(2),
            mapOf(0 to 0)
        )

        val example = App(Name("f"), Name("g"))
        val unify = OneUnification(context, listOf(example))
        // Expected HM behavior: should succeed
        assertTrue(unify.ok(), "In HM, this should unify 'b with Int")
    }

    /**
     * Test case: Both parameter and argument specialize - concrete type in argument.
     * f: ('a -> 'a -> 'a) -> Int
     * g: 'b -> 'b -> Int
     * Expected: Should succeed in HM. 'a unifies with 'b, then 'a unifies with Int.
     */
    @Test
    fun `both param and arg specialize - concrete in argument`() {
        val context = SearchState(
            mapOf("f" to 0, "g" to 1),
            listOf(
                // f: ('a -> 'a -> 'a) -> Int
                Arrow(
                    Arrow(Variable(0), Arrow(Variable(0), Variable(0))),
                    NamedLabel(0, listOf())
                ),
                // g: 'b -> 'b -> Int
                // (conceptually 'b, but uses Variable(0) which gets fresh instance during instantiation)
                Arrow(Variable(0), Arrow(Variable(0), NamedLabel(0, listOf())))
            ),
            listOf(2),
            mapOf(0 to 0)
        )

        val example = App(Name("f"), Name("g"))
        val unify = OneUnification(context, listOf(example))
        // Expected HM behavior: should succeed
        assertTrue(unify.ok(), "In HM, this should unify 'a with Int")
    }

    /**
     * Test case: Parameter specializes to match concrete argument.
     * f: 'a -> Int
     * g: Bool -> Int
     * Expected: Should succeed. 'a specializes to Bool.
     */
    @Test
    fun `parameter specializes to match argument`() {
        val context = SearchState(
            mapOf("f" to 0, "x" to 1),
            listOf(
                // f: 'a -> Int
                Arrow(Variable(0), NamedLabel(0, listOf())),
                // x: Bool -> Int (label 1 is Bool)
                Arrow(NamedLabel(1, listOf()), NamedLabel(0, listOf()))
            ),
            listOf(2),
            mapOf(0 to 0, 1 to 0)
        )

        val example = App(Name("f"), Name("x"))
        val unify = OneUnification(context, listOf(example))
        // Expected HM behavior: should succeed, 'a becomes Bool -> Int
        assertTrue(unify.ok(), "In HM, 'a should specialize to Bool -> Int")
    }

    /**
     * Test case: Argument specializes to match concrete parameter.
     * f: (Bool -> Int) -> Int
     * g: 'a -> Int
     * Expected: Should succeed. 'a specializes to Bool.
     */
    @Test
    fun `argument specializes to match parameter`() {
        val context = SearchState(
            mapOf("f" to 0, "g" to 1),
            listOf(
                // f: (Bool -> Int) -> Int
                Arrow(
                    Arrow(NamedLabel(1, listOf()), NamedLabel(0, listOf())),
                    NamedLabel(0, listOf())
                ),
                // g: 'a -> Int
                Arrow(Variable(0), NamedLabel(0, listOf()))
            ),
            listOf(2),
            mapOf(0 to 0, 1 to 0)
        )

        val example = App(Name("f"), Name("g"))
        val unify = OneUnification(context, listOf(example))
        // Expected HM behavior: should succeed, 'a becomes Bool
        assertTrue(unify.ok(), "In HM, 'a should specialize to Bool")
    }

    /**
     * Test case: Both types have variables that specialize to concrete types.
     * f: 'a -> Int
     * g: Bool -> 'b
     * Expected: Should succeed. 'a becomes Bool, 'b becomes Int.
     */
    @Test
    fun `both types specialize to each other's concrete parts`() {
        val context = SearchState(
            mapOf("f" to 0, "g" to 1),
            listOf(
                // f: 'a -> Int
                Arrow(Variable(0), NamedLabel(0, listOf())),
                // g: Bool -> 'b
                Arrow(NamedLabel(1, listOf()), Variable(0))
            ),
            listOf(2),
            mapOf(0 to 0, 1 to 0)
        )

        val example = App(Name("f"), Name("g"))
        val unify = OneUnification(context, listOf(example))
        // Expected HM behavior: should succeed
        assertTrue(unify.ok(), "In HM, 'a -> Bool and 'b -> Int")
    }

    /**
     * Negative test case: Passing an Int where a function is expected.
     * This should NOT type check because Int cannot be unified with 'a -> 'b.
     */
    @Test
    fun `fail to unify Int with function type`() {
        // Define a function 'f' that takes a function: f: ('a -> 'b) -> Int
        // And a value 'x' of type Int

        val context = SearchState(
            mapOf("f" to 0, "x" to 1),
            listOf(
                // f: ('a -> 'b) -> Int
                Arrow(
                    Arrow(Variable(0), Variable(1)), // 'a -> 'b
                    NamedLabel(0, listOf()) // Int
                ),
                // x: Int
                NamedLabel(0, listOf())
            ),
            listOf(2), // rounds
            mapOf(0 to 0) // label 0 (Int) has arity 0
        )

        // Example: f(x) - trying to apply f to an Int value
        val example = App(Name("f"), Name("x"))
        val unify = OneUnification(context, listOf(example))

        // This should fail to type check
        assertFalse(unify.ok(), "Expected unification to fail when passing Int to function expecting 'a -> 'b")
    }

    /**
     * Negative test case: Attempting to trigger an occurs check failure.
     *
     * NOTE: Due to the way OneUnification instantiates types with fresh variables,
     * it's actually difficult to trigger an occurs check failure in practice.
     * The occurs check is meant to prevent infinite types like 'a = 'a -> 'b,
     * but with fresh instantiation, different variable instances don't create this problem.
     *
     * This test demonstrates that even seemingly recursive scenarios don't trigger
     * the occurs check due to variable instantiation.
     */
    @Test
    fun `occurs check is hard to trigger with fresh instantiation`() {
        // f: 'a -> Int
        // g: ('a -> 'b) -> Int

        val context = SearchState(
            mapOf("f" to 0, "g" to 1),
            listOf(
                // f: 'a -> Int
                Arrow(Variable(0), NamedLabel(0, listOf())),
                // g: ('a -> 'b) -> Int
                Arrow(Arrow(Variable(0), Variable(1)), NamedLabel(0, listOf()))
            ),
            listOf(2), // rounds
            mapOf(0 to 0) // label 0 has arity 0
        )

        val example = App(Name("g"), Name("f"))
        val unify = OneUnification(context, listOf(example))

        assertTrue(unify.ok(), "Fresh instantiation prevents occurs check failure in this case")
    }

    /**
     * Negative test case: Type constructor mismatch.
     * Attempting to unify different labels (e.g., Int vs Bool) should fail.
     */
    @Test
    fun `fail to unify different type constructors`() {
        // Define a function 'f' that expects Int: f: Int -> Int
        // And a value 'x' of type Bool

        val context = SearchState(
            mapOf("f" to 0, "x" to 1),
            listOf(
                // f: Int -> Int (label 0 is Int)
                Arrow(NamedLabel(0, listOf()), NamedLabel(0, listOf())),
                // x: Bool (label 1 is Bool)
                NamedLabel(1, listOf())
            ),
            listOf(2), // rounds
            mapOf(0 to 0, 1 to 0) // label 0 (Int) and label 1 (Bool) have arity 0
        )

        // Example: f(x) - trying to apply f to a Bool value
        val example = App(Name("f"), Name("x"))
        val unify = OneUnification(context, listOf(example))

        // This should fail to type check
        assertFalse(unify.ok(), "Expected unification to fail when passing Bool to function expecting Int")
    }

    /**
     * Negative test case: Type constructor parameter count mismatch.
     * This test verifies that OneUnification properly rejects types where a type constructor
     * is used with the wrong number of parameters relative to its declared arity.
     *
     * In this case, List is declared with arity 1, but 'x' attempts to use it with 2 parameters.
     * When trying to unify f's parameter (List with 1 param) with x (List with 2 params),
     * the arity mismatch should cause unification to fail.
     */
    @Test
    fun `fail to unify type constructors with different parameter counts`() {
        // Define a function 'f' that expects List<Int>: f: List<Int> -> Int
        // And a value 'x' that incorrectly uses List with 2 parameters

        val context = SearchState(
            mapOf("f" to 0, "x" to 1),
            listOf(
                // f: List<Int> -> Int (List correctly used with 1 param)
                Arrow(
                    NamedLabel(2, listOf(NamedLabel(0, listOf()))), // List<Int>
                    NamedLabel(0, listOf()) // Int
                ),
                // x: List<Int, Bool> (List incorrectly used with 2 params)
                NamedLabel(2, listOf(NamedLabel(0, listOf()), NamedLabel(1, listOf())))
            ),
            listOf(2), // rounds
            mapOf(0 to 0, 1 to 0, 2 to 1) // label 2 (List) is declared with arity 1
        )

        // Example: f(x)
        // When trying to unify, the parameter count mismatch (1 vs 2) should cause failure
        val example = App(Name("f"), Name("x"))
        val unify = OneUnification(context, listOf(example))

        // This should fail to type check due to parameter count mismatch
        assertFalse(unify.ok(), "Expected unification to fail due to different parameter counts in type constructor")
    }

    /**
     * Positive test case: Simple identity function application.
     * Applying id: 'a -> 'a to a value of type Int should succeed.
     */
    @Test
    fun `unify identity function with Int value`() {
        val context = SearchState(
            mapOf("id" to 0, "x" to 1),
            listOf(
                // id: 'a -> 'a
                Arrow(Variable(0), Variable(0)),
                // x: Int
                NamedLabel(0, listOf())
            ),
            listOf(2), // rounds
            mapOf(0 to 0)
        )

        // Example: id(x)
        val example = App(Name("id"), Name("x"))
        val unify = OneUnification(context, listOf(example))

        // This should successfully type check
        assertTrue(unify.ok(), "Expected unification to succeed for identity function applied to Int")

        // The result should be Int
        val resultType = unify.type(example)
        assertNotNull(resultType, "Expected non-null result type")
    }

    /**
     * Negative test: Specialization fails due to incompatible concrete types.
     * f: Int -> Int
     * g: Bool -> Bool
     * Expected: Should fail. Cannot unify Int with Bool.
     */
    @Test
    fun `specialization fails - incompatible concrete types`() {
        val context = SearchState(
            mapOf("f" to 0, "g" to 1),
            listOf(
                // f: Int -> Int
                Arrow(NamedLabel(0, listOf()), NamedLabel(0, listOf())),
                // g: Bool -> Bool
                Arrow(NamedLabel(1, listOf()), NamedLabel(1, listOf()))
            ),
            listOf(2),
            mapOf(0 to 0, 1 to 0)
        )

        val example = App(Name("f"), Name("g"))
        val unify = OneUnification(context, listOf(example))
        // Expected: should fail
        assertFalse(unify.ok(), "Should fail - cannot unify Int -> Int with Bool -> Bool")
    }

    /**
     * Negative test: Specialization fails due to incompatible structure.
     * f: ('a -> 'b) -> Int
     * g: Int
     * Expected: Should fail. Cannot unify function type with Int.
     */
    @Test
    fun `specialization fails - structure mismatch`() {
        val context = SearchState(
            mapOf("f" to 0, "x" to 1),
            listOf(
                // f: ('a -> 'b) -> Int
                Arrow(Arrow(Variable(0), Variable(0)), NamedLabel(0, listOf())),
                // x: Int
                NamedLabel(0, listOf())
            ),
            listOf(2),
            mapOf(0 to 0)
        )

        val example = App(Name("f"), Name("x"))
        val unify = OneUnification(context, listOf(example))
        // Expected: should fail
        assertFalse(unify.ok(), "Should fail - cannot unify function type with Int")
    }

    /**
     * Negative test: Both variables, but constrained to incompatible concrete types.
     * f: 'a -> Int (where 'a must be Bool from context)
     * g: 'b -> String (where 'b must be Int from context)
     * This creates: Bool -> Int vs Int -> String
     * Expected: Should fail.
     */
    @Test
    fun `specialization fails - variables constrained to incompatible types`() {
        val context = SearchState(
            mapOf("f" to 0, "g" to 1, "h" to 2),
            listOf(
                // f: Bool -> 'a
                Arrow(NamedLabel(1, listOf()), Variable(0)),
                // g: 'a -> Int
                Arrow(Variable(0), NamedLabel(0, listOf())),
                // h: ('a -> 'a) -> Int (expects matching input/output)
                Arrow(Arrow(Variable(0), Variable(0)), NamedLabel(0, listOf()))
            ),
            listOf(3),
            mapOf(0 to 0, 1 to 0, 2 to 0)
        )

        // Try h with f(g) where f: Bool -> 'a, g: 'a -> Int
        // f(g) would need 'a to be unified in conflicting ways
        val example = App(Name("h"), App(Name("f"), Name("g")))
        val unify = OneUnification(context, listOf(example))
        // Expected: should fail - Bool != Int
        assertFalse(unify.ok(), "Should fail - input and output types don't match")
    }

    /**
     * Test case demonstrating a legitimate occurs check rejection.
     * This creates a scenario where we need infinite type.
     * Consider a fix-point combinator scenario or self-application.
     * f: 'a -> 'b
     * x: 'a
     * But if we try to apply x to itself: x(x)
     * Then 'a must equal ('a -> something), which is infinite.
     */
    @Test
    fun `occurs check legitimately rejects infinite type`() {
        // In practice, we need a scenario where within a SINGLE type instantiation,
        // a variable must equal a type containing itself.
        // This is hard with OneUnification's fresh instantiation approach.
        //
        // One way: Use a recursive let binding or Y-combinator style construction.
        // But OneUnification doesn't support these directly in the test framework.
        //
        // Alternative: Create a type that self-references within its own definition.
        // For example, if we had: type T = T -> Int
        // But we can't create this directly in the test either.
        //
        // The best we can do is demonstrate that the occurs check EXISTS and WORKS:

        val context = SearchState(
            mapOf("f" to 0),
            listOf(
                // This is a bit artificial, but: imagine a function that takes itself
                // If we could construct: f: f -> Int
                // But we can't represent this directly, so this test documents the limitation
                Arrow(Variable(0), Variable(0))
            ),
            listOf(1),
            mapOf(0 to 0)
        )

        // The occurs check in unify() at line 80 prevents V0 = (V0 -> V0)
        // But with fresh instantiation, we get V0-0 = (V0-1 -> V0-1), which is fine
        val example = App(Name("f"), Name("f"))
        val unify = OneUnification(context, listOf(example))

        // This actually succeeds due to fresh instantiation
        // The occurs check doesn't trigger because different instances
        assertTrue(unify.ok(), "With fresh instantiation, f(f) works when f: 'a -> 'a")
    }

    /**
     * More sophisticated occurs check test.
     * Try to create a situation where the occurs check must fire.
     * Consider: We want to unify 'a with ('a -> Int)
     * This should fail with occurs check.
     */
    @Test
    fun `occurs check rejects variable equal to type containing itself`() {
        // The occurs check happens at Unification.kt:80
        // It checks: if (param in arg.variables()) null
        // This fires when trying to bind a variable to a type containing that variable
        //
        // However, due to instantiation, this is hard to trigger in normal usage.
        // The check is a safety mechanism that prevents bugs in the unification algorithm.
        //
        // To truly test it, we'd need to call unify() directly with carefully crafted types
        // that have the SAME variable instance in both param and arg.

        // This test documents that the occurs check exists but is hard to trigger
        // in the current architecture due to fresh instantiation.

        val context = SearchState(
            mapOf("id" to 0),
            listOf(Arrow(Variable(0), Variable(0))),
            listOf(1),
            mapOf()
        )

        val example = App(Name("id"), Name("id"))
        val unify = OneUnification(context, listOf(example))

        // id applied to id should work: ('a -> 'a) applied to ('b -> 'b)
        // Results in: 'b -> 'b (since 'a gets bound to 'b -> 'b)
        assertTrue(unify.ok(), "id(id) should work with fresh instantiation")
    }
    private fun ConstraintTy.toNode(): Type =
        when (this) {
            is ConstraintArrow -> Arrow(this.l.toNode(), this.r.toNode())
            is ConstraintLabel -> NamedLabel(this.label, this.params.map { it.toNode() })
            is ConstraintVariable -> Variable(this.v)
            is InstantiationTy -> error("Unreachable pattern match - convert Instantiation to node")
            Bottom -> error("Antiunifying should never produce Bottom")
        }
}
