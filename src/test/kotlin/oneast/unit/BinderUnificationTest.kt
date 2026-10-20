package oneast.unit

import oneast.*
import org.junit.jupiter.api.Test
import query.Example
import testutil.unsignedExample
import util.CheckingGroundTruthOracle
import util.stateFromContext
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

/** Type checking lambdas and lets, which follows Hindley-Milner. */
class BinderUnificationTest {
    private val a = Variable(0)
    private val b = Variable(1)
    private val I = NamedLabel(0, listOf())
    private val B = NamedLabel(1, listOf())
    private fun list(t: Type) = NamedLabel(2, listOf(t))
    private fun pair(l: Type, r: Type) = NamedLabel(3, listOf(l, r))

    private val types =
        mapOf(
            "Num" to I,
            "true" to B,
            "nil" to list(a),
            "cons" to Arrow(a, Arrow(list(a), list(a))),
            "pair" to Arrow(a, Arrow(b, pair(a, b))),
        )
    private val context = stateFromContext(types)

    private fun ok(program: String) = OneUnification(context, listOf(unsignedExample(program))).ok

    private fun type(program: Example) = OneUnification(context, emptyList()).type(program)

    private fun type(program: String) = type(unsignedExample(program))

    @Test
    fun `a let-bound name can be used at different types`() {
        assertTrue(ok("(let id = (fun x -> x) in (pair (id Num) (id true)))"))
    }

    @Test
    fun `a lambda parameter cannot`() {
        assertFalse(ok("(fun id -> pair (id Num) (id true))"))
        assertFalse(ok("((fun id -> pair (id Num) (id true)) (fun x -> x))"))
    }

    @Test
    fun `a let does not generalize a parameter it mentions`() {
        assertFalse(ok("(fun y -> (let z = y in (pair (cons Num z) (cons true z))))"))
        assertTrue(ok("(fun y -> (let z = y in (pair (cons Num z) (cons Num z))))"))
    }

    @Test
    fun `a let's value must type-check even if it is not used`() {
        assertFalse(ok("(let x = (Num Num) in true)"))
    }

    @Test
    fun `self-application fails the occurs check`() {
        assertFalse(ok("(fun x -> x x)"))
    }

    @Test
    fun `names follow the innermost binder`() {
        // The parameter x shadows the let's x
        assertTrue(ok("(let x = Num in (fun x -> x true))"))
        // The let's value is outside its own scope, so x there is the parameter
        assertEquals(Arrow(list(I), list(I)), type("(fun x -> (let x = (cons Num x) in x))"))
        // A binder shadows a component of the same name
        assertEquals(Arrow(a, a), type("(fun cons -> cons)"))
    }

    @Test
    fun `types of lambdas and lets`() {
        assertEquals(Arrow(a, a), type("(fun x -> x)"))
        assertEquals(Arrow(a, Arrow(b, a)), type("(fun x y -> x)"))
        assertEquals(pair(I, B), type("(let id = (fun x -> x) in (pair (id Num) (id true)))"))
        assertEquals(Arrow(Arrow(I, a), a), type("(fun f -> f Num)"))
    }

    @Test
    fun `separate uses of a component have separate variables`() {
        assertEquals(pair(list(a), list(b)), type("(pair nil nil)"))
        assertEquals(pair(list(a), list(b)), type("(let n = nil in pair n n)"))
        assertEquals(pair(list(a), list(a)), type("((fun n -> pair n n) nil)"))
    }

    // The dependency analysis compares examples by these types. If both uses of nil shared a
    // variable, pair nil nil would wrongly equal the lambda, whose two lists must be the same.
    @Test
    fun `the ground truth oracle tells separate uses of a component apart`() {
        val oracle = CheckingGroundTruthOracle(types)
        fun equal(x: String, y: String) = oracle.equal(unsignedExample(x), unsignedExample(y))
        assertFalse(equal("(pair nil nil)", "((fun n -> pair n n) nil)"))
        assertTrue(equal("(pair nil nil)", "(let n = nil in pair n n)"))
    }

    // Each use of a let-bound name has its own instances of the holes in the value, and they stay
    // instances of those holes, so refining a hole constrains every use.
    @Test
    fun `each use of a let-bound name is its own instance of the holes in it`() {
        val f = TypeHole()
        val holed = stateFromContext(types + ("f" to f))
        fun check(program: String) = OneUnification(holed, listOf(unsignedExample(program)))

        val u = check("(let g = f in (pair (g Num) (g true)))")
        // One for checking the value on its own, one for each use.
        assertEquals(3, u.classesOf(f).toSet().size)
        assertEquals(HoleConstructor.Arrow, u.holeConstructor(f))
        val mark = u.mark()
        assertTrue(u.refine(f, Arrow(a, a)))
        u.rewindTo(mark)
        assertFalse(u.refine(f, Arrow(I, I)))

        // A lambda's g is one type, so it fails before f is refined at all.
        assertFalse(check("((fun g -> (pair (g Num) (g true))) f)").ok)
        assertTrue(check("((fun g -> (pair (g Num) (g Num))) f)").ok)
    }
}
