package oneast

import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.EnumSource
import query.App
import query.Example
import query.Name
import testutil.ocaml.*
import testutil.unsignedExample
import kotlin.random.Random
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

/** The other ways to ask OCaml whether an expression type-checks must answer like ocamlc. */
class OCamlGroundTruthTest {
    private val ocamlc = OCamlChecker()
    private val typer = OCamlTyper()
    private val toplevel = OCamlToplevel()

    /** Each check on its own and all of them as one batch, which ocamlc can only do as a whole. */
    private fun assertAgree(sources: List<String>) {
        val disagreements = sources.mapNotNull { src ->
            val expected = ocamlc.isValid(src).isValid
            val got = mapOf("typer" to typer.validSource(src), "toplevel" to toplevel.validSource(src))
            got.filterValues { it != expected }.keys.takeIf { it.isNotEmpty() }?.let { "$it disagree on $src (ocamlc: $expected)" }
        }
        assertTrue(disagreements.isEmpty(), disagreements.joinToString("\n"))
    }

    @Test
    fun `the value restriction and running the code don't matter`() {
        val wellTyped =
            listOf(
                "compare (fun x -> x)",
                "compare (fun x -> x) (fun x -> x)", // raises when run
                "ref []",
                "List.map (fun x -> x)",
                "(fun x -> x) (fun x -> x)",
                "exit 0", // would end the toplevel if run
                "read_line ()", // would wait for input if run
            )
        val illTyped =
            listOf(
                "compare 1 true",
                "succ true",
                "(",
                // Operators written without spaces open comments: one left open, one empty
                "(*.) 1. 2.",
                "(**) 1. 2.",
                "\"unterminated",
            )
        assertAgree(wellTyped + illTyped)
        wellTyped.forEach { assertTrue(typer.validSource(it), it) }
    }

    @Test
    fun `every subexpression of the OCaml benchmarks' examples`() {
        val (examples, _) = loadFromExsFiles(ocamlModuleGroups.flatten())
        assertAgree(examples.flatMap { it.subexprs() }.distinct().map { it.toString() })
    }

    @Test
    fun `random expressions`() {
        val (examples, types) = loadFromExsFiles(ocamlModuleGroups.take(2).flatten())
        val names = (examples.flatMap { it.names } + types.keys).distinct().sorted()
        val random = Random(0)
        fun gen(depth: Int): Example =
            if (depth == 0 || random.nextInt(3) == 0) Name(names[random.nextInt(names.size)])
            else App(gen(depth - 1), gen(depth - 1))
        assertAgree(List(300) { gen(4).toString() })
    }

    @ParameterizedTest
    @EnumSource(OCamlGroundTruth::class)
    fun `a batch fails if any expression in it does`(kind: OCamlGroundTruth) {
        val truth = kind.create()
        val ok = listOf("(succ Num)", "(not true)", "(compare (compare Num))").map { unsignedExample(it) }
        assertTrue(truth.allValid(ok))
        assertEquals(false, truth.allValid(ok + unsignedExample("(succ true)")))
        assertEquals(false, truth.allValid(listOf(unsignedExample("(succ true)")) + ok))
        // More than the toplevel puts in one phrase
        assertTrue(truth.allValid(List(250) { unsignedExample("(succ Num)") }))
    }
}
