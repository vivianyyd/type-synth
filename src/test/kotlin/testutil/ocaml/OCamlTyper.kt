package testutil.ocaml

import query.Example
import util.GroundTruth
import util.join
import java.io.File
import java.nio.file.Files
import java.nio.file.StandardCopyOption

/**
 * Type-checks expressions with a server around OCaml's own type checker ([source]), started once
 * and fed one expression per line. A check costs a line written to a pipe, not a compiler process.
 * Nothing is compiled or run, and an expression is typed without being bound, so the value
 * restriction never rejects a well-typed one.
 *
 * @param packages findlib packages whose modules the expressions may use
 * @param opens modules opened around each expression
 * @param source how examples are written as OCaml
 */
class OCamlTyper(
    private val packages: List<String> = emptyList(),
    opens: List<String> = listOf("Stdlib"),
    private val source: OCamlSource = OCamlSource(),
) : GroundTruth {
    // Stdlib is open already
    private val prefix = opens.filter { it != "Stdlib" }.joinToString("") { "let open $it in " }

    private val process: Process by lazy {
        val includeDirs =
            if (packages.isEmpty()) emptyList()
            else output(ProcessBuilder(listOf("ocamlfind", "query", "-r", "-format", "%d") + packages))
                .lines().filter { it.isNotBlank() }.distinct()
        ProcessBuilder(listOf(binary().path) + includeDirs)
            .redirectError(ProcessBuilder.Redirect.to(File("/dev/null")))
            .start()
            .also { p -> Runtime.getRuntime().addShutdownHook(Thread { p.destroy() }) }
    }
    private val input by lazy { process.outputStream.bufferedWriter() }
    private val answers by lazy { process.inputStream.bufferedReader() }

    override fun valid(example: Example): Boolean = validSource(source.of(example))

    /** Whether [expr], OCaml source, type-checks. */
    @Synchronized
    fun validSource(expr: String): Boolean {
        require('\n' !in expr) { "The typer reads one expression per line: $expr" }
        input.write("$prefix($expr)\n")
        input.flush()
        return when (val answer = answers.readLine()) {
            "ok" -> true
            "err" -> false
            else -> error("Unexpected answer from the OCaml typer: $answer")
        }
    }

    companion object {
        private val source = File(join("src", "test", "ocaml", "typer.ml"))
        private val binary = File(join("build", "ocaml-typer", "typer"))

        /**
         * Builds the server if it is missing or older than its source. It is built in a directory of
         * its own and moved into place, so runs building it at once (`bench --jobs`) can't see half
         * a binary, and the compiler's other output stays out of the source tree.
         */
        @Synchronized
        private fun binary(): File {
            if (binary.isFile && binary.lastModified() >= source.lastModified()) return binary
            binary.parentFile.mkdirs()
            val dir = Files.createTempDirectory(binary.parentFile.toPath(), "build").toFile()
            try {
                source.copyTo(File(dir, source.name))
                output(
                    ProcessBuilder(
                        "ocamlfind", "ocamlopt", "-package", "compiler-libs.common", "-linkpkg", source.name,
                        "-o", "typer"
                    )
                        .directory(dir)
                )
                Files.move(
                    File(dir, "typer").toPath(), binary.toPath(),
                    StandardCopyOption.REPLACE_EXISTING, StandardCopyOption.ATOMIC_MOVE
                )
            } finally {
                dir.deleteRecursively()
            }
            return binary
        }

        /** Runs [command] to completion and returns its output, failing if it fails. */
        private fun output(command: ProcessBuilder): String {
            val p = command.redirectErrorStream(true).start()
            val out = p.inputStream.bufferedReader().readText()
            check(p.waitFor() == 0) { "${command.command().joinToString(" ")} failed:\n$out" }
            return out
        }
    }
}
