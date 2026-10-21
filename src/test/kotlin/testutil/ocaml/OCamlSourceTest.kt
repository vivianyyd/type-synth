package testutil.ocaml

import org.junit.jupiter.api.Test
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.EnumSource
import testutil.unsignedExample
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class OCamlSourceTest {
    // ---------------------------------------------------------------- labels

    private val labels = mapOf("f" to listOf(null, "l"))

    @Test
    fun `a labelled argument is written with its label`() {
        assertEquals("f x ~l:(g y)", withLabels(unsignedExample("(f x (g y))"), labels).toString())
        // Under-applied, so there is no argument to label
        assertEquals("f x", withLabels(unsignedExample("(f x)"), labels).toString())
        // Labels inside arguments too
        assertEquals("h (f x ~l:(y))", withLabels(unsignedExample("(h (f x y))"), labels).toString())
    }

    @ParameterizedTest
    @EnumSource(OCamlGroundTruth::class)
    fun `OCaml accepts a labelled value applied positionally in an example`(kind: OCamlGroundTruth) {
        val ex = unsignedExample("(Option.value (Option.some Num) Num)")
        assertTrue(kind.create(OCamlSource(labels = mapOf("Option.value" to listOf(null, "default")))).valid(ex))
        // Without the label, OCaml passes Num to Option.value's result instead
        assertFalse(kind.create(OCamlSource()).valid(ex))
        assertTrue(kind.create(stdlibSource).valid(ex))
    }

    // ---------------------------------------------------------------- dummies

    @Test
    fun `dummy values replace whole names only`() {
        assertEquals(
            "String.length (String.make 1 'a')",
            OCamlSource().of(unsignedExample("(String.length (String.make Num Char))"))
        )
        assertEquals("Unit.equal () ()", OCamlSource().of(unsignedExample("(Unit.equal Unit Unit)")))
    }
}
