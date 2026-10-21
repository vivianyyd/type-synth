package testutil.ocaml

import query.Example
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
 * @param source how examples are written as OCaml
 */
class OCamlChecker(
    private val packages: List<String> = emptyList(),
    private val opens: List<String> = listOf("Stdlib"),
    private val source: OCamlSource = OCamlSource(),
) : GroundTruth {
    override fun valid(example: Example): Boolean = isValid(source.of(example)).isValid

    /** Compiles all of [examples] in one file, which fails if any one of them does. */
    override fun allValid(examples: Collection<Example>): Boolean =
        examples.isEmpty() || compile(examples.map { source.of(it) }).isValid

    private val preamble: String = opens.joinToString("\n") { "open $it" } + "\n"

    /** Check if a single expression is valid OCaml code. */
    fun isValid(expr: String): TypeCheckResult = compile(listOf(expr))

    /** Compiles each of [exprs] as its own top-level binding, all in one file. */
    private fun compile(exprs: List<String>): TypeCheckResult {
        val expr = exprs.joinToString("\n")
        val tempFile = Files.createTempFile("ocaml_check_", ".ml").toFile()

        try {
            // Write preamble + expressions
            tempFile.writeText(preamble + exprs.joinToString("") { "let _ = ($it)\n" })

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
