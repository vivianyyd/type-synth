package oneast

import kotlin.test.Test
import kotlin.test.assertNotNull
import testutil.ocaml.OcamlTypeParser

class OcamlTypeParserTest {

    private val parser = OcamlTypeParser()

    @Test
    fun `parses postfix list type application`() {
        // 'a list is postfix application: list('a), not 'a applied to list
        val result = parser.parseSignature("val length : 'a list -> int")
        assertNotNull(result["length"])
    }

    @Test
    fun `parses chained postfix type constructors`() {
        // 'a list list means list(list('a))
        val result = parser.parseSignature("val concat : 'a list list -> 'a list")
        assertNotNull(result["concat"])
    }

    @Test
    fun `parses postfix option type`() {
        val result = parser.parseSignature("val nth_opt : 'a list -> int -> 'a option")
        assertNotNull(result["nth_opt"])
    }

    @Test
    fun `parses 12-list types file`() {
        // 12-list.types contains: val (@) : 'a list -> 'a list -> 'a list
        val file = java.io.File("src/test/input/ocaml-stdlib/12-list.types")
        val result = OcamlTypeParser().parseSignatures(file.readText())
        assertNotNull(result["(@)"])
    }

    @Test
    fun `parses selected signatures from 50-list-mod types`() {
        // Signatures without product types or multi-arg constructors
        val signatures = """
            val length : 'a list -> int
            val is_empty : 'a list -> bool
            val cons : 'a -> 'a list -> 'a list
            val singleton : 'a -> 'a list
            val hd : 'a list -> 'a
            val tl : 'a list -> 'a list
            val rev : 'a list -> 'a list
            val flatten : 'a list list -> 'a list
            val sort_uniq : ('a -> 'a -> int) -> 'a list -> 'a list
        """.trimIndent()
        val result = OcamlTypeParser().parseSignatures(signatures)
        assertNotNull(result["length"])
        assertNotNull(result["rev"])
        assertNotNull(result["flatten"])
        assertNotNull(result["sort_uniq"])
    }
}
