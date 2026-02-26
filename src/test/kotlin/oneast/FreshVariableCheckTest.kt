package oneast

import org.junit.jupiter.api.Test
import kotlin.test.assertEquals
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

        assertEquals(setOf(0, 1), t1.variablesBeforeLastParam())
        assertEquals(setOf(2), t1.lastParamVariables())
        assertEquals(setOf(0), t2.variablesBeforeLastParam())
        assertEquals(setOf(1), t2.lastParamVariables())
        assertEquals(setOf(0, 1), t3.variablesBeforeLastParam())
        assertEquals(setOf(1, 2), t3.lastParamVariables())

        assertTrue(t1.freshVariableInOutput())
        assertTrue(t2.freshVariableInOutput())
        assertTrue(t3.freshVariableInOutput())
    }
}
