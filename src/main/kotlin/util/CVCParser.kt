package util

fun parse(input: String): List<String> {
    val trimmed = input.trim().removePrefix("[").removeSuffix("]")
    val result = mutableListOf<String>()
    val sb = StringBuilder()
    var depth = 0
    for (c in trimmed) {
        when (c) {
            ',' -> {
                if (depth == 0) {
                    result.add(sb.toString().trim())
                    sb.clear()
                } else sb.append(c)
            }
            '(' -> {
                depth++
                sb.append(c)
            }
            ')' -> {
                depth--
                sb.append(c)
            }
            else -> sb.append(c)
        }
    }
    if (sb.isNotEmpty()) result.add(sb.toString().trim())
    return result
}
