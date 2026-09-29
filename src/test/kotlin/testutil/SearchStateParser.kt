package testutil

import oneast.*

/**
 * Reads a state written as `name=type ; name=type ; ...`, with each type written the way [Type]
 * prints: `V0`, `L1[V0, _]`, `(V0 -> V1) -> V0`. `_` is a type hole, and `.L` and `.` are blanks
 * that are and are not label-only. Each hole or blank written is a different one.
 */
fun parseSearchState(s: String): SearchState {
    val entries = s.split(" ; ").map { it.substringBefore("=") to TypeParser(it.substringAfter("=")).parse() }
    return SearchState(
        names = entries.withIndex().associate { it.value.first to it.index },
        types = entries.map { it.second },
        labelArities = mapOf()
    )
}

private class TypeParser(private val s: String) {
    private var i = 0

    fun parse(): Type = type().also {
        skipSpaces()
        require(i == s.length) { "Unexpected ${s.substring(i)} in $s" }
    }

    private fun type(): Type {
        val from = atom()
        skipSpaces()
        if (!s.startsWith("->", i)) return from
        i += 2
        return Arrow(from, type())
    }

    private fun atom(): Type {
        skipSpaces()
        return when (s[i++]) {
            '(' -> type().also { expect(')') }
            'V' -> Variable(number())
            'L' -> {
                val label = number()
                expect('[')
                val params = mutableListOf<Type>()
                skipSpaces()
                if (s[i] != ']') {
                    params.add(type())
                    skipSpaces()
                    while (s[i] == ',') {
                        i++
                        params.add(type())
                        skipSpaces()
                    }
                }
                expect(']')
                NamedLabel(label, params)
            }
            '_' -> TypeHole()
            '.' ->
                if (i < s.length && s[i] == 'L') {
                    i++
                    Blank(labelOnly = true)
                } else Blank(labelOnly = false)
            else -> error("Unexpected ${s[i - 1]} at ${i - 1} in $s")
        }
    }

    private fun number(): Int {
        val start = i
        while (i < s.length && s[i].isDigit()) i++
        return s.substring(start, i).toInt()
    }

    private fun expect(c: Char) {
        skipSpaces()
        require(s[i] == c) { "Expected $c at $i in $s" }
        i++
    }

    private fun skipSpaces() {
        while (i < s.length && s[i] == ' ') i++
    }
}
