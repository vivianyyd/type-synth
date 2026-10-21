package testutil.ocaml

import query.App
import query.Example
import query.Lam
import query.Let
import query.Name
import util.GroundTruth
import java.io.File
import java.nio.file.Files
import java.util.concurrent.TimeUnit
import kotlin.streams.toList

data class TypeCheckResult(
    val isValid: Boolean,
    val errorMessage: String? = null,
    val expression: String
)

/**
 * Type-checks OCaml expressions by compiling them individually.
 *
 * @param packages List of OCaml packages to import (e.g., ["base", "core", "lwt"])
 * @param opens List of modules to open in the preamble (e.g., ["Stdlib", "Base"])
 * @param thunkLets Whether examples are checked as [thunkLets] makes them, so that OCaml's value
 *   restriction never applies. Without it, the examples must avoid the value restriction; see
 *   src/test/input/ocaml-stdlib/exs/README.md.
 */
class OCamlChecker(
    private val packages: List<String> = emptyList(),
    private val opens: List<String> = listOf("Stdlib"),
    private val thunkLets: Boolean = false,
) : GroundTruth {
    override fun valid(example: Example): Boolean =
        isValid(withDummies(if (thunkLets) thunkLets(example) else example).toString()).isValid

    private val preamble: String = opens.joinToString("\n") { "open $it" } + "\n"

    /** Check if a single expression is valid OCaml code. */
    fun isValid(expr: String): TypeCheckResult {
        val tempFile = Files.createTempFile("ocaml_check_", ".ml").toFile()

        try {
            // Write preamble + expression
            tempFile.writeText(preamble + "let _ = ($expr)\n")

            // Build command
            val command = buildCommand(tempFile)

            // Run compiler
            val process = ProcessBuilder(command).redirectErrorStream(true).start()

            val output = process.inputStream.bufferedReader().readText()
            val exitCode = process.waitFor(10, TimeUnit.SECONDS)

            if (!exitCode) {
                process.destroyForcibly()
                return TypeCheckResult(false, "Compilation timeout", expr)
            }

            val isValid = process.exitValue() == 0
            val errorMsg = if (!isValid) output.trim() else null

            return TypeCheckResult(isValid, errorMsg, expr)
        } finally {
            // Clean up temp files
            tempFile.delete()
            File(tempFile.path.replace(".ml", ".cmi")).delete()
            File(tempFile.path.replace(".ml", ".cmo")).delete()
        }
    }

    private fun buildCommand(file: File): List<String> {
        return if (packages.isEmpty()) {
            listOf("ocamlc", "-c", file.absolutePath)
        } else {
            listOf(
                "ocamlfind",
                "ocamlc",
                "-package",
                packages.joinToString(","),
                "-c",
                file.absolutePath
            )
        }
    }
}

/** OCaml values that the examples name by their type, as `Num` for an int. */
private val dummies =
    mapOf("Num" to "1", "Str" to "\"s\"", "Char" to "'a'", "Flt" to "1.", "Nil" to "[]")

/** [e] with each name in [dummies] replaced by its value. Binders are never one, being lowercase. */
private fun withDummies(e: Example): Example =
    when (e) {
        is Name -> dummies[e.name]?.let(::Name) ?: e
        is App -> App(withDummies(e.fn), withDummies(e.arg))
        is Lam -> Lam(e.param, withDummies(e.body))
        is Let -> Let(e.name, withDummies(e.value), withDummies(e.body))
    }

/**
 * [example] with each `let x = v in body` made `let x = fun _ -> v in body`, and each use of x in
 * body made `x ()`.
 *
 * OCaml generalizes a let-bound name only if its value is a syntactic value (a name, a lambda, ...),
 * where Hindley-Milner generalizes every let. `fun _ -> v` is a value, and each `x ()` has a fresh
 * instance of v's type, as each use of x has in Hindley-Milner. So ocamlc accepts the result exactly
 * when Hindley-Milner accepts [example], as far as lets go.
 */
fun thunkLets(example: Example): Example = thunkLets(example, emptySet())

private val unit = Name("()")

/** [lets] are the let-bound names in scope. */
private fun thunkLets(e: Example, lets: Set<String>): Example =
    when (e) {
        is Name -> if (e.name in lets) App(e, unit) else e
        is App -> App(thunkLets(e.fn, lets), thunkLets(e.arg, lets))
        is Lam -> Lam(e.param, thunkLets(e.body, lets - e.param))
        is Let -> Let(e.name, Lam("_", thunkLets(e.value, lets)), thunkLets(e.body, lets + e.name))
    }
