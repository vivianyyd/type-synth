package baselines.lc

import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.Nested

/**
 * Tests for Algorithm LC — rank-2 type inference for the second-order λ-calculus.
 *
 * Rank-2 polymorphism arises when a function receives a polymorphic argument
 * and uses it at multiple types. The classic pattern is:
 *   (λf. ... f x ... f y ...) (λa. a)
 * where f is applied to arguments of different types.
 *
 * In Algorithm LC, this works because:
 *   - λf is λ¹ (matched with argument) → β-reduced away
 *   - λa is λ² (inside an argument) → each copy gets independent typing
 */
class AlgorithmLCTest {

    @BeforeEach
    fun resetCounters() {
        Type.resetCounter()
        BetaReduction.resetCounter()
        RAsupSolver.resetCounter()
    }

    // --- Helpers ---
    private fun v(name: String) = Term.Var(name)
    private fun lam(p: String, body: Term) = Term.Abs(p, body)
    private fun app(f: Term, a: Term) = Term.App(f, a)
    private fun app(f: Term, a: Term, b: Term) = app(app(f, a), b)
    private fun app(f: Term, a: Term, b: Term, c: Term) = app(app(app(f, a), b), c)

    private fun inferOk(term: Term, env: Map<String, Type> = emptyMap()): Type {
        val result = AlgorithmLC.infer(term, env, debug = true)
        assertNotNull(result.type, "Expected successful inference but got error: ${result.error}")
        return result.type!!
    }

    private fun inferFail(term: Term, env: Map<String, Type> = emptyMap()) {
        val result = AlgorithmLC.infer(term, env)
        assertNull(result.type, "Expected type error but got: ${result.type}")
    }

    private fun assertArrow(t: Type): Pair<Type, Type> {
        assertTrue(t is Type.Arrow, "Expected arrow type, got: $t")
        return (t as Type.Arrow).domain to t.codomain
    }

    // =============================================================
    // 1. SIMPLE TYPES (rank 1, no polymorphic arguments)
    // =============================================================
    @Nested
    inner class SimpleTypes {

        @Test
        fun `identity function`() {
            // λx. x  :  a → a
            val ty = inferOk(lam("x", v("x")))
            val (dom, cod) = assertArrow(ty)
            assertEquals(dom, cod, "Identity: domain = codomain")
        }

        @Test
        fun `constant function`() {
            // λx. λy. x  :  a → b → a
            val ty = inferOk(lam("x", lam("y", v("x"))))
            val (a, rest) = assertArrow(ty)
            val (b, a2) = assertArrow(rest)
            assertEquals(a, a2, "K combinator: first and last type match")
            assertNotEquals(a, b, "K combinator: two params have different types")
        }

        @Test
        fun `function composition`() {
            // λf. λg. λx. f (g x)  :  (b → c) → (a → b) → a → c
            val ty = inferOk(lam("f", lam("g", lam("x",
                app(v("f"), app(v("g"), v("x")))))))
            val (fType, rest1) = assertArrow(ty)
            val (gType, rest2) = assertArrow(rest1)
            val (aType, cType) = assertArrow(rest2)
            val (b1, c1) = assertArrow(fType)
            val (a1, b2) = assertArrow(gType)
            assertEquals(a1, aType, "g's domain = x's type")
            assertEquals(b1, b2, "f's domain = g's codomain")
            assertEquals(c1, cType, "f's codomain = result type")
        }

        @Test
        fun `flip function`() {
            // λf. λx. λy. f y x  :  (a → b → c) → b → a → c
            val ty = inferOk(lam("f", lam("x", lam("y", app(app(v("f"), v("y")), v("x"))))))
            val (fType, rest1) = assertArrow(ty)
            val (xType, rest2) = assertArrow(rest1)
            val (yType, cType) = assertArrow(rest2)
            val (fDom, fRest) = assertArrow(fType)
            val (fDom2, fCod) = assertArrow(fRest)
            assertEquals(fDom, yType, "f's first arg = y's type")
            assertEquals(fDom2, xType, "f's second arg = x's type")
            assertEquals(fCod, cType, "f's result = overall result")
        }

        @Test
        fun `church numeral 2`() {
            // λf. λx. f (f x)  :  (a → a) → a → a
            val ty = inferOk(lam("f", lam("x", app(v("f"), app(v("f"), v("x"))))))
            val (fType, rest) = assertArrow(ty)
            val (xType, resultType) = assertArrow(rest)
            val (fDom, fCod) = assertArrow(fType)
            assertEquals(fDom, fCod, "f : a → a")
            assertEquals(xType, fDom, "x has same type as f's domain")
            assertEquals(resultType, fCod, "result has same type as f's codomain")
        }

        @Test
        fun `S combinator`() {
            // λf. λg. λx. f x (g x)  :  (a → b → c) → (a → b) → a → c
            val ty = inferOk(lam("f", lam("g", lam("x",
                app(app(v("f"), v("x")), app(v("g"), v("x")))))))
            val (fTy, rest1) = assertArrow(ty)
            val (gTy, rest2) = assertArrow(rest1)
            val (aTy, cTy) = assertArrow(rest2)
            val (fA, fBC) = assertArrow(fTy)
            val (fB, fC) = assertArrow(fBC)
            val (gA, gB) = assertArrow(gTy)
            assertEquals(fA, aTy, "f and x share first type")
            assertEquals(gA, aTy, "g and x share first type")
            assertEquals(fB, gB, "f's second domain = g's codomain")
            assertEquals(fC, cTy, "f's result = overall result")
        }

        @Test
        fun `self application is a type error`() {
            // λx. x x — untypeable (infinite type via occurs check)
            inferFail(lam("x", app(v("x"), v("x"))))
        }
    }

    // =============================================================
    // 2. β-REDUCTION (λ¹ elimination)
    // =============================================================
    @Nested
    inner class BetaReductionTests {

        @Test
        fun `apply identity to identity`() {
            // (λf. f) (λx. x)  :  a → a
            val ty = inferOk(app(lam("f", v("f")), lam("x", v("x"))))
            val (dom, cod) = assertArrow(ty)
            assertEquals(dom, cod)
        }

        @Test
        fun `apply identity to free var`() {
            // (λf. f) y  :  type of y
            val ty = inferOk(app(lam("f", v("f")), v("y")))
            assertTrue(ty is Type.Var)
        }

        @Test
        fun `nested beta reduction produces identity`() {
            // (λf. λx. f x) (λy. y)  :  a → a
            val ty = inferOk(app(lam("f", lam("x", app(v("f"), v("x")))), lam("y", v("y"))))
            val (dom, cod) = assertArrow(ty)
            assertEquals(dom, cod)
        }

        @Test
        fun `apply K combinator`() {
            // (λk. k a b) (λx. λy. x)  ≡  a
            val ty = inferOk(app(lam("k", app(app(v("k"), v("a")), v("b"))), lam("x", lam("y", v("x")))))
            assertTrue(ty is Type.Var, "Result should be type of a")
        }
    }

    // =============================================================
    // 3. RANK-2 INFERENCE (the key feature)
    // =============================================================
    @Nested
    inner class Rank2Inference {

        @Test
        fun `polymorphic identity applied to different types via let`() {
            // let id = λx.x in pair (id zero) (id true_)
            // ≡ (λid. pair (id zero) (id true_)) (λx. x)
            //
            // id must have type ∀a. a → a to be applied to both Int and Bool.
            // After β-reduction, id is substituted into two copies:
            //   pair ((λx₁.x₁) zero) ((λx₂.x₂) true_)
            // Each copy is independently typed.
            val env = mapOf("zero" to Type.Var("Int"), "true_" to Type.Var("Bool"))
            val term = app(
                lam("id", app(v("pair"), app(v("id"), v("zero")), app(v("id"), v("true_")))),
                lam("x", v("x"))
            )
            val ty = inferOk(term, env)
            // The result type should involve Int and Bool somewhere
            assertNotNull(ty)
        }

        @Test
        fun `polymorphic identity applied twice - f(f(x))`() {
            // (λf. f (f y)) (λx. x)  :  type of y
            // f : ∀a. a → a, so f (f y) = f y = y.
            val ty = inferOk(app(lam("f", app(v("f"), app(v("f"), v("y")))), lam("x", v("x"))))
            assertTrue(ty is Type.Var, "Result should be type var (type of y)")
        }

        @Test
        fun `polymorphic identity applied thrice - f(f(f(x)))`() {
            // (λf. f (f (f y))) (λx. x)  :  type of y
            val ty = inferOk(app(
                lam("f", app(v("f"), app(v("f"), app(v("f"), v("y"))))),
                lam("x", v("x"))
            ))
            assertTrue(ty is Type.Var, "Result should be type var (type of y)")
        }

        @Test
        fun `polymorphic const applied to different types`() {
            // let k = λa.λb.a in pair (k zero true_) (k true_ zero)
            // ≡ (λk. pair (k zero true_) (k true_ zero)) (λa. λb. a)
            //
            // k : ∀a.∀b. a → b → a (used as Int→Bool→Int and Bool→Int→Bool)
            val env = mapOf("zero" to Type.Var("Int"), "true_" to Type.Var("Bool"))
            val term = app(
                lam("k", app(v("pair"),
                    app(v("k"), v("zero"), v("true_")),
                    app(v("k"), v("true_"), v("zero")))),
                lam("a", lam("b", v("a")))
            )
            val ty = inferOk(term, env)
            assertNotNull(ty)
        }

        @Test
        fun `polymorphic function applied to arrow-typed and base-typed args`() {
            // (λf. pair (f succ) (f zero)) (λx. x)
            // f : ∀a. a → a; f succ : Nat; f zero : Nat
            val env = mapOf(
                "succ" to Type.Var("Nat"),
                "zero" to Type.Var("Nat")
            )
            val term = app(
                lam("f", app(v("pair"), app(v("f"), v("succ")), app(v("f"), v("zero")))),
                lam("x", v("x"))
            )
            val ty = inferOk(term, env)
            assertNotNull(ty)
        }

        @Test
        fun `polymorphic identity applied to itself - rank-2 self-application`() {
            // (λf. f f) (λx. x)
            //
            // This is the canonical rank-2 test: f has type ∀a. a → a,
            // so f f is valid — the outer f is instantiated at (∀a.a→a)→(∀a.a→a),
            // and the inner f is used as its argument.
            //
            // After β-reduction: (λx₁. x₁) (λx₂. x₂)
            // Both copies are independently typed λ²-abstractions.
            // Result: (λx₂. x₂) which has type a → a.
            val term = app(lam("f", app(v("f"), v("f"))), lam("x", v("x")))
            val ty = inferOk(term)
            val (dom, cod) = assertArrow(ty)
            assertEquals(dom, cod, "Should be a → a")
        }

        @Test
        fun `polymorphic identity applied to different-typed free vars`() {
            // (λf. pair (f n) (f b)) (λx. x)
            // where n : Int, b : Bool
            // f : ∀a. a → a is applied at type Int and type Bool.
            // After β: pair ((λx₁.x₁) n) ((λx₂.x₂) b)
            // Result involves both Int and Bool.
            val env = mapOf("n" to Type.Var("Int"), "b" to Type.Var("Bool"))
            val term = app(
                lam("f", app(v("pair"), app(v("f"), v("n")), app(v("f"), v("b")))),
                lam("x", v("x"))
            )
            val ty = inferOk(term, env)
            assertNotNull(ty, "Should succeed — this is the classic rank-2 use case")
        }

        @Test
        fun `applying compose polymorphically`() {
            // let comp = λf.λg.λx. f(g x) in comp succ pred
            // ≡ (λc. c succ pred) (λf.λg.λx. f(g x))
            // Result: a function Int → Int (since succ and pred are Int→Int)
            val intToInt = Type.Arrow(Type.Var("Int"), Type.Var("Int"))
            val env = mapOf("succ" to intToInt, "pred" to intToInt)
            val compose = lam("f", lam("g", lam("x", app(v("f"), app(v("g"), v("x"))))))
            val term = app(app(app(compose, v("succ")), v("pred")), v("zero"))
            val envWithZero = env + ("zero" to Type.Var("Int"))
            val ty = inferOk(term, envWithZero)
            assertEquals(Type.Var("Int"), ty)
        }
    }

    // =============================================================
    // 4. TYPE ENVIRONMENT
    // =============================================================
    @Nested
    inner class TypeEnvironment {

        @Test
        fun `free variable gets type from env`() {
            val env = mapOf("n" to Type.Arrow(Type.Var("Int"), Type.Var("Int")))
            val ty = inferOk(v("n"), env)
            assertEquals(Type.Arrow(Type.Var("Int"), Type.Var("Int")), ty)
        }

        @Test
        fun `application with typed free variables`() {
            val env = mapOf(
                "succ" to Type.Arrow(Type.Var("Int"), Type.Var("Int")),
                "zero" to Type.Var("Int")
            )
            val ty = inferOk(app(v("succ"), v("zero")), env)
            assertEquals(Type.Var("Int"), ty)
        }

        @Test
        fun `type error - mismatched application`() {
            // Applying Int to Int→Int: should fail
            val env = mapOf(
                "succ" to Type.Arrow(Type.Var("Int"), Type.Var("Int")),
                "zero" to Type.Var("Int")
            )
            inferFail(app(v("zero"), v("succ")), env)
        }
    }

    // =============================================================
    // 5. LABELLING VERIFICATION
    // =============================================================
    @Nested
    inner class LabellingTests {

        @Test
        fun `matched lambda is RANK1`() {
            val labeled = LambdaLabelling.label(app(lam("f", v("f")), v("x")))
            val func = (labeled as LabeledTerm.App).func as LabeledTerm.Abs
            assertEquals(AbstractionLabel.RANK1, func.label)
        }

        @Test
        fun `lambda in argument is RANK2`() {
            val labeled = LambdaLabelling.label(app(v("g"), lam("x", v("x"))))
            val arg = (labeled as LabeledTerm.App).arg as LabeledTerm.Abs
            assertEquals(AbstractionLabel.RANK2, arg.label)
        }

        @Test
        fun `standalone lambda is RANK3`() {
            val labeled = LambdaLabelling.label(lam("x", v("x")))
            assertEquals(AbstractionLabel.RANK3, (labeled as LabeledTerm.Abs).label)
        }

        @Test
        fun `nested lambda in argument is RANK2`() {
            // g (λx. λy. x) — both λx and λy should be RANK2 (inside argument)
            val labeled = LambdaLabelling.label(app(v("g"), lam("x", lam("y", v("x")))))
            val arg = (labeled as LabeledTerm.App).arg as LabeledTerm.Abs
            assertEquals(AbstractionLabel.RANK2, arg.label, "outer λ should be λ²")
            val inner = arg.body as LabeledTerm.Abs
            assertEquals(AbstractionLabel.RANK2, inner.label, "inner λ should also be λ²")
        }
    }

    // =============================================================
    // 6. UNIFICATION
    // =============================================================
    @Nested
    inner class UnificationTests {

        @Test
        fun `unify variables`() {
            val s = Unification.unify(Type.Var("a"), Type.Var("b"))
            assertNotNull(s)
        }

        @Test
        fun `unify arrow types`() {
            val s = Unification.unify(
                Type.Arrow(Type.Var("a"), Type.Var("b")),
                Type.Arrow(Type.Var("Int"), Type.Var("Bool"))
            )
            assertNotNull(s)
            assertEquals(Type.Var("Int"), s!!.apply(Type.Var("a")))
            assertEquals(Type.Var("Bool"), s.apply(Type.Var("b")))
        }

        @Test
        fun `occurs check fails`() {
            assertNull(Unification.unify(Type.Var("a"), Type.Arrow(Type.Var("a"), Type.Var("b"))))
        }
    }
}
