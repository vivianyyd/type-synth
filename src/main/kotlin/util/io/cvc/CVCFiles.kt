package util.io.cvc

import bench.Count
import bench.Stats
import util.*
import java.io.BufferedReader
import java.io.BufferedWriter
import java.io.File
import java.io.IOException
import java.nio.file.Files
import java.util.concurrent.ConcurrentLinkedQueue

/**
 * Set by the system property typesynth.cvcDir to keep every query and answer. Each process gets a
 * new run-* directory in there, because files are named by state id and state ids restart every
 * process. Unset, nothing is written.
 */
private val cvcDir: File? by lazy {
    System.getProperty("typesynth.cvcDir")?.let { keepIn ->
        File(keepIn).mkdirs()
        Files.createTempDirectory(File(keepIn).toPath(), "run-").toFile().also { dir ->
            File(dir, "input").mkdirs()
            File(dir, "output").mkdirs()
        }
    }
}

/** Must match cvc_worker.py. */
private const val QUERY_END = "#--- end of query ---"
private const val ANSWER_END = "#--- end of answer ---"

/** One python3 running cvc_worker.py. Answers one query at a time. */
private class Worker {
    private val proc: Process
    private val stdin: BufferedWriter
    private val stdout: BufferedReader
    /** Read on its own thread, so a full stderr pipe can't block the worker. */
    private val stderr = StringBuffer()

    init {
        // So queries can import cardinality.py
        val pb = ProcessBuilder("python3", join("src", "main", "python", "cvc_worker.py"))
            .directory(File(System.getProperty("user.dir")))
        pb.environment()["PYTHONPATH"] = join("src", "main", "python", "input")
        proc = pb.start()
        stdin = proc.outputStream.bufferedWriter()
        stdout = proc.inputStream.bufferedReader()
        Thread {
            proc.errorStream.bufferedReader().forEachLine { stderr.appendLine(it) }
        }.apply { isDaemon = true }.start()
        Runtime.getRuntime().addShutdownHook(Thread { proc.destroy() })
    }

    private fun died(): Nothing {
        proc.waitFor()
        throw IllegalStateException("The cvc5 worker exited with ${proc.exitValue()}:\n$stderr")
    }

    /** What the query printed. Throws if the query raised or the worker died. */
    fun answer(query: String, name: String): String {
        try {
            stdin.write(query)
            if (!query.endsWith("\n")) stdin.write("\n")
            stdin.write("$QUERY_END\n")
            stdin.flush()
        } catch (e: IOException) {
            died()
        }
        val status = stdout.readLine() ?: died()
        val answer = StringBuilder()
        while (true) {
            val line = stdout.readLine() ?: died()
            if (line == ANSWER_END) break
            answer.appendLine(line)
        }
        if (status != "ok") throw IllegalStateException("cvc5 query $name failed:\n$answer")
        return answer.toString()
    }
}

/**
 * Workers not running a query. labelArities runs in parallel, so a call takes an idle worker or
 * starts a new one. A worker that throws is not put back.
 */
private val idle = ConcurrentLinkedQueue<Worker>()

/** What cvc5 printed for the query [content], or null when it has no solution. */
fun callCVC(content: String, testName: String): String? {
    val start = System.nanoTime()
    cvcDir?.let { write(File(it, "input/cvc-$testName.py").path, content) }
    val worker = idle.poll() ?: Worker()
    val out = worker.answer(content, testName)
    idle.add(worker)
    Stats.inc(Count.SOLVER_CALLS)
    Stats.add(Count.SOLVER_NANOS, System.nanoTime() - start)
    // What cvc5.pythonic's solve prints when cvc5 answers unknown
    if ("failed to solve" in out)
        throw IllegalStateException("cvc5 gave up on query $testName:\n$out")
    if ("no solution" in out) return null
    cvcDir?.let { write(File(it, "output/cvc-$testName.py").path, out) }
    return out
}
