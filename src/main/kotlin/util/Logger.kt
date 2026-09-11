package util

import java.io.File
import java.io.PrintStream
import java.time.LocalTime
import java.util.*

const val MAX_VERBOSITY = 5

/*
TODO log file that has a list of runs in CSV format that this appends to
 */

class Logger(
    configuration: Config,
    logToFile: Boolean,
    logFilename: String = "type.log",
    private val printImmediately: Boolean = false,
    private val logTimestamps: Boolean = true,
    private val logVerbosity: Boolean = true,
    val verbosity: Int = MAX_VERBOSITY
) : Writer() {
    private val stages = Stack<Pair<String, Long>>()
    private val logStream =
        if (logToFile) PrintStream(File(logFilename).outputStream(), false) else System.out
    private val startTime = System.currentTimeMillis()
    private var lastLog = startTime

    init {
        logStream.println(configuration)
        if (printImmediately) logStream.flush()
    }

    fun log(message: String, level: Int = 0) {
        lastLog = System.currentTimeMillis()
        if (level <= verbosity) {
            val time = if (logTimestamps) "[${LocalTime.now()}]" else ""
            val lvl = if (level > 0 && logVerbosity) " [$level]" else ""
            logStream.println("$time$lvl\t$message")
        }
        if (printImmediately) logStream.flush()
    }

    private fun elapsed() = log("Elapsed time: ${System.currentTimeMillis() - startTime} ms")

    fun start(stage: String) {
        stages.push(stage to System.currentTimeMillis())
        log("BEG $stage")
        indent()
    }

    fun stop(stage: String, printCounts: Boolean = true) {
        val (s, t) = stages.pop()
        if (s != stage) error("Stopped a stage that wasn't started: $stage")
        dedent()
        log("END $stage : ${System.currentTimeMillis() - t} ms")
        if (printCounts) log(
            counts.entries
                .filter { it.value > 50 }
                .joinToString(separator = "\n", prefix = "Counts:\n"))
        elapsed()
    }

    private val counts = mutableMapOf<String, Int>()

    fun count(value: String) {
        if (verbosity > 4) {
            if (value in counts) counts[value] = counts[value]!! + 1 else counts[value] = 1
        }
        if (System.currentTimeMillis() - lastLog > 20 * 1000) {
            log(
                counts.entries.joinToString(
                    separator = "\n\t",
                    prefix = "Counts so far:\n\t"
                )
            )
            elapsed()
        }
    }

    fun finish() {
        while (!stages.empty()) {
            val (s, _) = stages.peek()
            stop(s, printCounts = false)
        }
        log(counts.entries.joinToString(separator = "\n", prefix = "Counts:\n"))
        log("Total time: ${System.currentTimeMillis() - startTime} ms")
    }

    fun fail(message: String = "") {
        finish()
        error(message)
    }
}

fun <T> Logger.time(name: String, block: () -> T): T {
    start(name)
    val result = block()
    stop(name)
    return result
}
