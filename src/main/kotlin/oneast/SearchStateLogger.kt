package oneast

import com.squareup.moshi.Moshi
import com.squareup.moshi.kotlin.reflect.KotlinJsonAdapterFactory
import org.slf4j.Logger
import org.slf4j.LoggerFactory
import java.util.concurrent.ConcurrentHashMap

enum class SearchStateLogMode {
    OFF,
    LOG,
    LOG_IF,
    COUNT_UNIQUE
}

class SearchStateLogger(
    private val mode: SearchStateLogMode,
    loggerName: String = "SearchStateLogger"
) {
    private val logger: Logger by lazy { LoggerFactory.getLogger(loggerName) }
    private val seenKeys = ConcurrentHashMap.newKeySet<Any>()
    private val nullKey = Any()
    private val uniqueCountName = "$loggerName.uniqueCount"
    private val defaultFormatter: (Any?) -> String = { it?.toString() ?: "null" }
    private val moshi = Moshi.Builder().add(KotlinJsonAdapterFactory()).build()

    private fun trackUnique(key: Any?) {
        seenKeys.add(key ?: nullKey)
    }

    private fun isEnabled(level: Int): Boolean =
        when {
            level <= 0 -> logger.isInfoEnabled
            level == 1 -> logger.isDebugEnabled
            else -> logger.isTraceEnabled
        }

    private fun logMessage(level: Int, message: String) {
        when {
            level <= 0 -> logger.info(message)
            level == 1 -> logger.debug(message)
            else -> logger.trace(message)
        }
    }

    private fun logThrowable(level: Int, message: String, throwable: Throwable) {
        when {
            level <= 0 -> logger.error(message, throwable)
            level == 1 -> logger.warn(message, throwable)
            level == 2 -> logger.info(message, throwable)
            level == 3 -> logger.debug(message, throwable)
            else -> logger.trace(message, throwable)
        }
    }

    private fun toJson(value: Any?): String =
        when (value) {
            null -> "null"
            else -> runCatching { moshi.adapter(value.javaClass).toJson(value) }.getOrDefault(
                value.toString()
            )
        }

    private fun logValue(
        value: Any?,
        level: Int,
        condition: ((Any?) -> Boolean)?,
        formatter: ((Any?) -> String)?,
        keySelector: ((Any?) -> Any)?
    ) {
        when (mode) {
            SearchStateLogMode.OFF -> Unit
            SearchStateLogMode.LOG -> {
                if (isEnabled(level)) {
                    logMessage(level, formatter?.invoke(value) ?: defaultFormatter(value))
                }
            }
            SearchStateLogMode.LOG_IF -> {
                if ((condition?.invoke(value) ?: false) && isEnabled(level)) {
                    logMessage(level, formatter?.invoke(value) ?: defaultFormatter(value))
                }
            }
            SearchStateLogMode.COUNT_UNIQUE -> trackUnique(keySelector?.invoke(value) ?: value)
        }
    }

    fun log(
        state: SearchState,
        level: Int = 0,
        condition: ((SearchState) -> Boolean)? = null,
        formatter: ((SearchState) -> String)? = null,
        keySelector: ((SearchState) -> Any)? = null
    ) =
        logValue(
            state,
            level,
            condition?.let { predicate -> { value -> predicate(value as SearchState) } },
            formatter?.let { format -> { value -> format(value as SearchState) } },
            keySelector?.let { selector -> { value -> selector(value as SearchState) } }
        )

    fun logAny(
        value: Any?,
        level: Int = 0,
        condition: ((Any?) -> Boolean)? = null,
        formatter: ((Any?) -> String)? = null,
        keySelector: ((Any?) -> Any)? = null
    ) = logValue(value, level, condition, formatter, keySelector)

    fun logJson(
        state: SearchState,
        level: Int = 0,
        condition: ((SearchState) -> Boolean)? = null,
        keySelector: ((SearchState) -> Any)? = null
    ) = log(state, level, condition, formatter = { toJson(it) }, keySelector = keySelector)

    fun logAnyJson(
        value: Any?,
        level: Int = 0,
        condition: ((Any?) -> Boolean)? = null,
        keySelector: ((Any?) -> Any)? = null
    ) = logAny(value, level, condition, formatter = { toJson(it) }, keySelector = keySelector)

    fun logStructured(
        fields: Map<String, Any?>,
        level: Int = 0,
        condition: ((Map<String, Any?>) -> Boolean)? = null
    ) = logAny(
        fields,
        level,
        condition = { condition?.invoke(fields) ?: true },
        formatter = { toJson(it) }
    )

    fun uniqueCount(): Int = seenKeys.size

    fun flushUniqueCount(level: Int = 0) {
        if (mode == SearchStateLogMode.OFF || !isEnabled(level)) return
        logMessage(level, "$uniqueCountName=${seenKeys.size}")
    }

    fun logException(message: String, throwable: Throwable, level: Int = 0) {
        if (mode == SearchStateLogMode.OFF) return
        logThrowable(level, message, throwable)
    }
}
