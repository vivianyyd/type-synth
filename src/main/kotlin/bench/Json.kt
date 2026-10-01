package bench

/** JSON text that is spliced in as is. */
class RawJson(val text: String)

/** Writes maps, lists, strings, numbers, booleans and null as JSON. Anything else as its string. */
object Json {
    fun write(value: Any?, pretty: Boolean = false): String =
        StringBuilder().also { write(value, it, if (pretty) 0 else -1) }.toString()

    /** [indent] < 0 writes everything on one line. */
    private fun write(value: Any?, sb: StringBuilder, indent: Int) {
        fun newline(level: Int) {
            if (indent >= 0) sb.append('\n').append("  ".repeat(level))
        }
        when (value) {
            null -> sb.append("null")
            is RawJson -> sb.append(value.text.trim())
            is Boolean -> sb.append(value)
            is Double -> sb.append(if (value.isFinite()) value.toString() else "null")
            is Float -> write(value.toDouble(), sb, indent)
            is Number -> sb.append(value)
            is Map<*, *> -> {
                sb.append('{')
                value.entries.forEachIndexed { i, (k, v) ->
                    if (i > 0) sb.append(',')
                    newline(indent + 1)
                    string(k.toString(), sb)
                    sb.append(if (indent >= 0) ": " else ":")
                    write(v, sb, if (indent >= 0) indent + 1 else -1)
                }
                if (value.isNotEmpty()) newline(indent)
                sb.append('}')
            }
            is Iterable<*> -> {
                val items = value.toList()
                // Short lists of scalars stay on one line
                val flat = indent < 0 || items.all { it !is Map<*, *> && it !is Iterable<*> }
                sb.append('[')
                items.forEachIndexed { i, v ->
                    if (i > 0) sb.append(if (flat && indent >= 0) ", " else ",")
                    if (!flat) newline(indent + 1)
                    write(v, sb, if (indent >= 0) indent + 1 else -1)
                }
                if (!flat && items.isNotEmpty()) newline(indent)
                sb.append(']')
            }
            is Array<*> -> write(value.toList(), sb, indent)
            is Enum<*> -> string(value.name, sb)
            else -> string(value.toString(), sb)
        }
    }

    private fun string(s: String, sb: StringBuilder) {
        sb.append('"')
        for (c in s) {
            when (c) {
                '"' -> sb.append("\\\"")
                '\\' -> sb.append("\\\\")
                '\n' -> sb.append("\\n")
                '\r' -> sb.append("\\r")
                '\t' -> sb.append("\\t")
                else -> if (c < ' ') sb.append(String.format("\\u%04x", c.code)) else sb.append(c)
            }
        }
        sb.append('"')
    }
}
