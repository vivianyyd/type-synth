package oneast

import org.junit.jupiter.api.Test
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class FreshVariableCheckTest {
    @Test
    fun `detects fresh variable on rhs`() {
        val a = Variable(0)
        val b = Variable(1)
        val c = Variable(2)
        val t1 = Arrow(a, Arrow(a, Arrow(b, c)))
        val t2 = Arrow(a, Arrow(a, Arrow(a, b)))
        val t3 = Arrow(a, Arrow(b, NamedLabel(0, listOf(b, c))))
        val t4 = Arrow(a, Arrow(b, NamedLabel(0, listOf(b, a))))
        val t5 = Arrow(Arrow(a, b), Arrow(a, Arrow(a, b)))
        val t6 = Arrow(Arrow(a, a), Arrow(c, Arrow(a, b)))

        assertTrue(t1.invalid())
        assertTrue(t2.invalid())
        assertTrue(t3.invalid())
        assertFalse(t4.invalid())
        assertFalse(t5.invalid())
        assertTrue(t6.invalid())
    }
}
