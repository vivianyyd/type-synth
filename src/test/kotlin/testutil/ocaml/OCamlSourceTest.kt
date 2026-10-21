package testutil.ocaml

import org.junit.jupiter.api.Test
import testutil.unsignedExample
import kotlin.test.assertEquals

class OCamlSourceTest {
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
