package oneast

import org.slf4j.Logger
import org.slf4j.LoggerFactory
import util.MAX_VERBOSITY
import java.io.PrintWriter
import java.io.StringWriter
import java.util.concurrent.ConcurrentHashMap

enum class SearchStateLogMode {
    OFF,
    LOG,
    LOG_IF,
    COUNT_UNIQUE
}

class SearchStateLogger(
    private val mode: SearchStateLogMode,
    private val verbosity: Int = MAX_VERBOSITY,
    loggerName: String = "SearchStateLogger"
) {
    private val logger: Logger by lazy { LoggerFactory.getLogger(loggerName) }
    private val seenKeys = ConcurrentHashMap.newKeySet<Any>()
    private val nullKey = Any()
    private val uniqueCountName = "$loggerName.uniqueCount"
    private val defaultFormatter: (Any?) -> String = { it?.toString() ?: "null" }

    private fun trackUnique(key: Any?) {
        seenKeys.add(key ?: nullKey)
    }

    fun log(
        state: SearchState,
        level: Int = 0,
        condition: ((SearchState) -> Boolean)? = null,
        formatter: ((SearchState) -> String)? = null,
        keySelector: ((SearchState) -> Any)? = null
    ) {
        if (level > verbosity) return
        val formatted = formatter?.invoke(state) ?: defaultFormatter(state)
        val key = keySelector?.invoke(state) ?: state
        when (mode) {
            SearchStateLogMode.OFF -> Unit
            SearchStateLogMode.LOG -> logger.info(formatted)
            SearchStateLogMode.LOG_IF ->
                if (condition?.invoke(state) == true) {
                    logger.info(formatted)
                }
            SearchStateLogMode.COUNT_UNIQUE -> trackUnique(key)
        }
    }

    fun logAny(
        value: Any?,
        level: Int = 0,
        condition: ((Any?) -> Boolean)? = null,
        formatter: ((Any?) -> String)? = null,
        keySelector: ((Any?) -> Any)? = null
    ) {
        if (level > verbosity) return
        val formatted = formatter?.invoke(value) ?: defaultFormatter(value)
        val key = keySelector?.invoke(value) ?: value
        when (mode) {
            SearchStateLogMode.OFF -> Unit
            SearchStateLogMode.LOG -> logger.info(formatted)
            SearchStateLogMode.LOG_IF ->
                if (condition?.invoke(value) == true) {
                    logger.info(formatted)
                }
            SearchStateLogMode.COUNT_UNIQUE -> trackUnique(key)
        }
    }

    fun uniqueCount(): Int = seenKeys.size

    fun flushUniqueCount(level: Int = 0) {
        if (level > verbosity) return
        logger.info("$uniqueCountName=${seenKeys.size}")
    }

    fun logException(message: String, throwable: Throwable, level: Int = 0) {
        if (mode == SearchStateLogMode.OFF || level > verbosity) return
        val sw = StringWriter()
        throwable.printStackTrace(PrintWriter(sw))
        logger.error("$message\n$sw")
    }
}
