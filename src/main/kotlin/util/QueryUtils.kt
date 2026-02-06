package util

import query.Query
import util.io.parseExamples

/** Convert a collection of S-expression strings into a [Query]. */
fun toQuery(lines: List<String>): Query = parseExamples(lines.filter { it.isNotBlank() })
