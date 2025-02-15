package util

sealed class SExpr {
    data class Atm(val value: String) : SExpr() {
        override fun toString(): String = value
    }
    data class Lst(val elements: List<SExpr>) : SExpr() {
        override fun toString(): String = "(${elements.joinToString(separator=" ")})"
    }
}

class SExprParser(private val input: String) {
    private var position = 0

    fun parse(): SExpr {
        skipWhitespace()
        return when {
            currentChar() == '(' -> parseList()
            else -> parseAtom()
        }
    }

    private fun parseList(): SExpr.Lst {
        consumeChar('(')
        val elements = mutableListOf<SExpr>()
        while (true) {
            skipWhitespace()
            if (currentChar() == ')') break
            elements.add(parse())
        }
        consumeChar(')')
        return SExpr.Lst(elements)
    }

    private fun parseAtom(): SExpr.Atm {
        val start = position
        while (position < input.length && !isDelimiter(currentChar())) {
            position++
        }
        if (start == position) throw IllegalArgumentException("Unexpected character at position $position")
        return SExpr.Atm(input.substring(start, position))
    }

    private fun skipWhitespace() {
        while (position < input.length && input[position].isWhitespace()) {
            position++
        }
    }

    private fun isDelimiter(ch: Char): Boolean {
        return ch.isWhitespace() || ch == '(' || ch == ')'
    }

    private fun currentChar(): Char {
        if (position >= input.length) throw IllegalArgumentException("Unexpected end of input")
        return input[position]
    }

    private fun consumeChar(expected: Char) {
        if (currentChar() != expected) {
            throw IllegalArgumentException("Expected '$expected' but found '${currentChar()}' at position $position")
        }
        position++
    }
}

fun main() {
    val input = "(def (square x) (* x x))"
    val parser = SExprParser(input)
    val result = parser.parse()
    println(result)
}