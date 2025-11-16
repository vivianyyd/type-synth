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
    private val logTimestamps: Boolean = true,
    private val logVerbosity: Boolean = true,
    val verbosity: Int = MAX_VERBOSITY
) : Writer() {
    private val stages = Stack<Pair<String, Long>>()
    private val logStream = if (logToFile) PrintStream(File(logFilename).outputStream(), true) else System.out

    init {
        logStream.println(configuration)
    }

    fun log(message: String, level: Int = 0) {
        if (level <= verbosity) {
            val time = if (logTimestamps) "[${LocalTime.now()}]" else ""
            val lvl = if (level > 0 && logVerbosity) " [$level]" else ""
            logStream.println("$time$lvl\t$message")
        }
    }

    fun start(stage: String) {
        stages.push(stage to System.currentTimeMillis())
        log("Started $stage")
        indent()
    }

    fun stop(stage: String) {
        val (s, t) = stages.pop()
        if (s != stage) error("Stopped a stage that wasn't started")
        dedent()
        log("Finished $stage after ${System.currentTimeMillis() - t} ms")
    }
}
