package testutil.ocaml

import java.io.File
import java.nio.file.Files
import java.util.concurrent.TimeUnit
import kotlin.streams.toList

data class TypeCheckResult(val isValid: Boolean, val errorMessage: String? = null)

/**
 * Type-checks OCaml expressions by compiling them individually.
 *
 * @param packages List of OCaml packages to import (e.g., ["base", "core", "lwt"])
 * @param opens List of modules to open in the preamble (e.g., ["Stdlib", "Base"])
 */
class OCamlChecker(
    private val packages: List<String> = emptyList(),
    private val opens: List<String> = listOf("Stdlib")
) {

    private val preamble: String = opens.joinToString("\n") { "open $it" } + "\n"

    private val desugarAtomsToDummies = listOf("Num" to "1", "Str" to "Dummy")

    private fun desugar(expr: String) =
        desugarAtomsToDummies.fold(expr) { acc, (from, to) -> acc.replace(from, to) }

    /** Check if a single expression is valid OCaml code. */
    fun isValid(expr: String): TypeCheckResult {
        val desugaredExpr = desugar(expr)

        val tempFile = Files.createTempFile("ocaml_check_", ".ml").toFile()

        try {
            // Write preamble + expression
            tempFile.writeText(preamble + "let _ = ($desugaredExpr)\n")

            // Build command
            val command = buildCommand(tempFile)

            // Run compiler
            val process = ProcessBuilder(command).redirectErrorStream(true).start()

            val output = process.inputStream.bufferedReader().readText()
            val exitCode = process.waitFor(10, TimeUnit.SECONDS)

            if (!exitCode) {
                process.destroyForcibly()
                return TypeCheckResult(false, "Compilation timeout")
            }

            val isValid = process.exitValue() == 0
            val errorMsg = if (!isValid) output.trim() else null

            return TypeCheckResult(isValid, errorMsg)
        } finally {
            // Clean up temp files
            tempFile.delete()
            File(tempFile.path.replace(".ml", ".cmi")).delete()
            File(tempFile.path.replace(".ml", ".cmo")).delete()
        }
    }

    /** Check multiple expressions. */
    fun checkAll(expressions: List<String>): List<TypeCheckResult> {
        return expressions.map { isValid(it) }
    }

    /** Check multiple expressions in parallel. */
    fun checkAllParallel(expressions: List<String>): List<TypeCheckResult> {
        return expressions.parallelStream().map { isValid(it) }.toList()
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

// Example usage
fun main() {
    // Example 1: Using only Stdlib (no external packages)
    val checker = OCamlChecker()

    val exprs =
        listOf(
            "1 + 2",
            "fun x ->\n  x + true", // type error: bool vs int
            "List.map succ [1;2;3]",
            "let f x y = x + y in f 1 2"
        )

    println("=== Stdlib only ===")
    exprs.forEach { expr ->
        val result = checker.isValid(expr)
        println("Expression: ${expr.replace("\n", "\\n")}")
        println("Valid: ${result.isValid}")
        if (!result.isValid) {
            println("Error: ${result.errorMessage}")
        }
        println()
    }

    // Example 2: Using Base library
    val baseChecker = OCamlChecker(packages = listOf("base"), opens = listOf("Base"))

    val baseExprs =
        listOf(
            "List.map ~f:Int.succ [1;2;3]",
            "String.concat ~sep:\",\" [\"a\"; \"b\"]",
            "Map.empty (module Int)" // Base-specific
        )

    println("=== With Base library ===")
    baseExprs.forEach { expr ->
        val result = baseChecker.isValid(expr)
        println("Expression: ${expr}")
        println("Valid: ${result.isValid}")
        println()
    }

    // Example 3: Check many expressions in parallel
    val manyExprs = (1..100).map { "1 + $it" }
    val parallelChecker = OCamlChecker()

    println("=== Checking ${manyExprs.size} expressions in parallel ===")
    val start = System.currentTimeMillis()
    val parallelResults = parallelChecker.checkAllParallel(manyExprs)
    val elapsed = System.currentTimeMillis() - start

    val validCount = parallelResults.count { it.isValid }
    println("Valid: $validCount/${parallelResults.size}")
    println("Time: ${elapsed}ms")
}
