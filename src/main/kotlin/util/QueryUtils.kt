package util

import query.Query
import query.parseExamples

/**
 * Convert a collection of S-expression strings into a [Query].
 */
fun toQuery(lines: List<String>): Query = parseExamples(lines.filter { it.isNotBlank() })

fun toQuery(contents: String): Query = toQuery(contents.lines())
