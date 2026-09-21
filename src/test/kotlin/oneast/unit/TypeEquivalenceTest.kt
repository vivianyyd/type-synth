package oneast.unit

import oneast.*
import org.junit.jupiter.api.Test
import kotlin.test.assertFailsWith
import kotlin.test.assertFalse
import kotlin.test.assertTrue

/** Tests for the type-level comparisons in `SearchStateEquivalence.kt`. */
class TypeEquivalenceTest {

    private val a = Variable(0)
    private val b = Variable(1)
    private val c = Variable(2)
    private fun l(label: Int, vararg params: Type) = NamedLabel(label, params.toList())

    // ----- equalUpToVariableRenaming: variables -----
    @Test
    fun `a type equals itself`() {
        assertTrue(equalUpToVariableRenaming(Arrow(a, l(0, b)), Arrow(a, l(0, b))))
    }

    @Test
    fun `variables may be renamed`() {
        assertTrue(equalUpToVariableRenaming(Arrow(a, a), Arrow(b, b)))
    }

    @Test
    fun `renaming must preserve which variables are shared`() {
        assertFalse(equalUpToVariableRenaming(Arrow(a, a), Arrow(a, b)))
        assertFalse(equalUpToVariableRenaming(Arrow(a, b), Arrow(a, a)))
    }

    @Test
    fun `renaming must be one-to-one`() {
        // 'a and 'b would both have to become 'c
        assertFalse(equalUpToVariableRenaming(Arrow(a, b), Arrow(c, c)))
    }

    @Test
    fun `renaming is shared across the whole type`() {
        val x = Arrow(a, Arrow(b, a))
        assertTrue(equalUpToVariableRenaming(x, Arrow(b, Arrow(c, b))))
        assertFalse(equalUpToVariableRenaming(x, Arrow(b, Arrow(c, c))))
    }

    // ----- equalUpToVariableRenaming: labels -----
    @Test
    fun `labels are not renamed`() {
        assertTrue(equalUpToVariableRenaming(l(0, a), l(0, b)))
        assertFalse(equalUpToVariableRenaming(l(0, a), l(1, a)))
        assertFalse(equalUpToVariableRenaming(l(0, l(1)), l(0, l(2))))
    }

    @Test
    fun `labels of different arity differ`() {
        assertFalse(equalUpToVariableRenaming(l(0, a), l(0, a, b)))
    }

    // ----- equalUpToVariableRenaming: holes and kinds -----
    @Test
    fun `any two holes are equal`() {
        assertTrue(equalUpToVariableRenaming(TypeHole(), TypeHole()))
        assertTrue(equalUpToVariableRenaming(TypeHole(), Blank(labelOnly = false)))
        assertTrue(equalUpToVariableRenaming(Blank(labelOnly = true), Blank(labelOnly = false)))
    }

    @Test
    fun `a hole is not a variable or a label`() {
        assertFalse(equalUpToVariableRenaming(TypeHole(), a))
        assertFalse(equalUpToVariableRenaming(TypeHole(), l(0)))
        assertFalse(equalUpToVariableRenaming(TypeHole(), Arrow(a, a)))
    }

    @Test
    fun `different kinds differ`() {
        assertFalse(equalUpToVariableRenaming(Arrow(a, b), l(0, a, b)))
        assertFalse(equalUpToVariableRenaming(a, l(0)))
    }

    // ----- ConstraintTy.toType -----
    @Test
    fun `toType drops instantiation ids`() {
        val t = ConstraintArrow(ConstraintVariable(0, 1), ConstraintVariable(0, 2))
        assertTrue(equalUpToVariableRenaming(Arrow(a, a), t.toType()))
    }

    @Test
    fun `toType keeps labels and structure`() {
        val t = ConstraintLabel(3, listOf(ConstraintVariable(0, 0), ConstraintLabel(1, listOf())))
        assertTrue(equalUpToVariableRenaming(l(3, a, l(1)), t.toType()))
    }

    @Test
    fun `toType rejects bottom`() {
        assertFailsWith<IllegalStateException> { Bottom.toType() }
        assertFailsWith<IllegalStateException> { ConstraintArrow(Bottom, Bottom).toType() }
    }

    // ----- equalInEmptyLabelContext -----
    @Test
    fun `labels may be renamed in an empty label context`() {
        val x = ConstraintLabel(0, listOf(ConstraintVariable(0, 0)))
        val y = ConstraintLabel(7, listOf(ConstraintVariable(4, 9)))
        assertTrue(equalInEmptyLabelContext(x, y))
    }

    @Test
    fun `label renaming in an empty label context must be consistent`() {
        val x = ConstraintArrow(ConstraintLabel(0, listOf()), ConstraintLabel(0, listOf()))
        val y = ConstraintArrow(ConstraintLabel(7, listOf()), ConstraintLabel(8, listOf()))
        assertFalse(equalInEmptyLabelContext(x, y))
    }
}
