package testutil.ocaml

import query.Name
import testutil.unsignedExample
import util.CheckingGroundTruthOracle
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.EnumSource
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

/**
 * Signatures and examples spell operators in several ways (`(*)`, `( * )`, `*`), and OCaml reads
 * `(*` as the start of a comment, so these check that both sides agree on one name for each
 * operator ([testutil.ocamlName]) and that [OCamlSource] writes it so that OCaml accepts it.
 */
class OperatorNameTest {
    private val stdlibTypes = OcamlTypeParser().let { parser ->
        ocamlTypesDir.listFiles()!!
            .filter { it.extension == "types" }
            .flatMap { parseTypesFile(parser, it).entries }
            .associate { it.key to it.value.type }
    }

    /** Every operator the stdlib signatures declare, by the name they give it. */
    private val stdlibOperators = stdlibTypes.keys.filter { it.startsWith("(") }

    @Test
    fun `the stdlib declares the operators these tests are about`() {
        val expected = listOf("(*)", "(*.)", "(**)", "(mod)", "(land)", "(:=)", "(~-)", "(!)")
        assertEquals(emptyList(), expected - stdlibOperators.toSet())
    }

    @Test
    fun `signatures name an operator the same however they space it`() {
        val types = OcamlTypeParser().parseSignatures(
            """
            val (*) : int -> int -> int
            val ( *. ) : float -> float -> float
            val ( mod ) : int -> int -> int
            val (land) : int -> int -> int
            val (  +  ) : int -> int -> int
            val (:=) : 'a ref -> 'a -> unit
            """.trimIndent()
        )
        assertEquals(listOf("(*)", "(*.)", "(mod)", "(land)", "(+)", "(:=)"), types.keys.toList())
    }

    @Test
    fun `examples name every stdlib operator as its signature does, however they space it`() {
        for (name in stdlibOperators) {
            val op = name.removeSurrounding("(", ")").trim()
            for (spelling in listOf(op, "($op)", "( $op )", "(($op))")) {
                assertEquals(Name(name), unsignedExample(spelling), "example $spelling")
            }
        }
    }

    @Test
    fun `operators that OCaml would read as a comment are written spaced`() {
        val source = OCamlSource()
        assertEquals("( * ) 1 1", source.of(unsignedExample("(* Num Num)")))
        assertEquals("( *. ) 1. 1.", source.of(unsignedExample("(( *. ) Flt Flt)")))
        assertEquals("( ** ) 1. 1.", source.of(unsignedExample("((**) Flt Flt)")))
        assertEquals("(+) 1 ((mod) 1 1)", source.of(unsignedExample("(+ Num (mod Num Num))")))
    }

    @ParameterizedTest
    @EnumSource(OCamlGroundTruth::class)
    fun `OCaml accepts every stdlib operator by its name`(kind: OCamlGroundTruth) {
        val ocaml = kind.create()
        assertEquals(emptyList(), stdlibOperators.filter { !ocaml.valid(Name(it)) })
    }

    @ParameterizedTest
    @EnumSource(OCamlGroundTruth::class)
    fun `operators in examples type-check as OCaml does`(kind: OCamlGroundTruth) {
        val oracle = CheckingGroundTruthOracle(stdlibTypes)
        val ocaml = kind.create()
        val valid = listOf(
            "(( * ) Num Num)", "(* Num Num)", "(( *. ) Flt Flt)", "((**) Flt Flt)",
            "(mod Num Num)", "((land) Num Num)", "((:=) (ref Num) Num)", "((!) (ref Num))",
            "((~-) Num)", "((~-.) Flt)", "((@) Nil Nil)", "((^) Str Str)", "((|>) Num succ)",
            "(( * ) (( * ) Num Num) Num)",
        )
        val invalid = listOf("(( * ) Flt Flt)", "(( *. ) Num Num)", "(mod Flt Num)", "((!) Num)")
        for (s in valid) {
            val example = unsignedExample(s)
            assertTrue(oracle.valid(example), "checker rejects $s")
            assertTrue(ocaml.valid(example), "OCaml rejects $s")
        }
        for (s in invalid) {
            val example = unsignedExample(s)
            assertTrue(!oracle.valid(example), "checker accepts $s")
            assertTrue(!ocaml.valid(example), "OCaml accepts $s")
        }
    }
}
