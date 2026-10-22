package testutil.ocaml

import query.Example
import util.GroundTruth
import java.io.File

/**
 * Type-checks expressions in one `ocaml` toplevel, started once and fed phrases.
 *
 * The toplevel runs what it is given, so each expression is wrapped in `fun () -> (...)`: then
 * nothing runs (`compare (fun x -> x) (fun x -> x)` is well-typed, but raises when run), and the
 * type is generalized rather than left with weak type variables.
 *
 * An expression that leaves a comment or string open would swallow the phrases after it, so it is
 * answered without the toplevel: it is a syntax error, as ocamlc says too.
 *
 * @param packages findlib packages whose modules the expressions may use
 * @param opens modules opened before any expression
 * @param source how examples are written as OCaml
 */
class OCamlToplevel(
    packages: List<String> = emptyList(),
    opens: List<String> = listOf("Stdlib"),
    private val source: OCamlSource = OCamlSource(),
) : GroundTruth {
    private val preamble =
        (if (packages.isEmpty()) "" else "#use \"topfind\";;\n#require \"${packages.joinToString(",")}\";;\n") +
                opens.joinToString("") { "open $it;;\n" }

    private val process: Process by lazy {
        ProcessBuilder("ocaml", "-noprompt", "-nopromptcont", "-color=never", "-w", "-a")
            .redirectErrorStream(true)
            .start()
            .also { p -> Runtime.getRuntime().addShutdownHook(Thread { p.destroy() }) }
    }
    private val input by lazy { process.outputStream.bufferedWriter() }
    private val output by lazy { process.inputStream.bufferedReader() }
    private var started = false

    override fun valid(example: Example): Boolean = validSource(source.of(example))

    /**
     * Several expressions in one phrase, which fails as a whole if any of them does. A phrase holds
     * at most [CHUNK] of them, so the toplevel never fills its output pipe while this is still
     * writing to its input.
     */
    @Synchronized
    override fun allValid(examples: Collection<Example>): Boolean {
        val sources = examples.map { source.of(it) }
        return sources.none { leavesLexerOpen(it) } &&
                sources.chunked(CHUNK).all { chunk -> ok(send(chunk.joinToString("\n") { item(it) } + ";;\n")) }
    }

    /** Whether [expr], OCaml source, type-checks. */
    @Synchronized
    fun validSource(expr: String): Boolean = !leavesLexerOpen(expr) && ok(send(item(expr) + ";;\n"))

    private fun item(src: String) = "let _ = fun () -> ($src)"

    private fun ok(printed: List<String>) = printed.none { it.startsWith("Error") }

    /** Sends [phrases] and returns what the toplevel printed for them. */
    private fun send(phrases: String): List<String> {
        if (!started) {
            started = true
            // Also skips the banner
            send(preamble)
        }
        input.write(phrases)
        input.write("let () = print_endline \"$MARKER\";;\n")
        input.flush()
        val printed = mutableListOf<String>()
        while (true) {
            val line = output.readLine() ?: error("The OCaml toplevel exited")
            if (line.trim() == MARKER) return printed
            printed.add(line)
        }
    }

    /**
     * Whether [src] ends inside a comment or a string. Knows OCaml's nested comments, strings with
     * escapes, and character literals like 'a' and '\n', which is all examples are made of.
     */
    private fun leavesLexerOpen(src: String): Boolean {
        var depth = 0
        var inString = false
        var i = 0
        while (i < src.length) {
            val c = src[i]
            val next = src.getOrNull(i + 1)
            when {
                inString -> if (c == '\\') i++ else if (c == '"') inString = false
                c == '"' -> inString = true
                c == '(' && next == '*' -> { depth++; i++ }
                depth > 0 && c == '*' && next == ')' -> { depth--; i++ }
                // Character literals, so that '"' doesn't start a string
                depth == 0 && c == '\'' && next == '\\' -> i = src.indexOf('\'', i + 2).let { if (it == -1) i else it }
                depth == 0 && c == '\'' && src.getOrNull(i + 2) == '\'' -> i += 2
            }
            i++
        }
        return depth > 0 || inString
    }

    private companion object {
        const val MARKER = "@@typesynth-done@@"
        const val CHUNK = 100
    }
}
