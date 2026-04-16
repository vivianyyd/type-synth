package testutil

import java.io.StringReader
import testutil.parser.SExprCupParser
import testutil.parser.SExprLexer

fun parseSExpr(s: String) = SExprParser(s).parse()

sealed class SExpr {
    data class Atm(val value: String) : SExpr() {
        override fun toString(): String = value
    }

    data class Lst(val elements: List<SExpr>) : SExpr() {
        override fun toString(): String = "(${elements.joinToString(separator = " ")})"
    }
}

private class SExprParser(private val input: String) {
    fun parse(): SExpr =
        try {
            val parser = SExprCupParser(SExprLexer(StringReader(input)))
            val result = parser.parse().value
            result as? SExpr
                ?: throw IllegalStateException("Parser produced unexpected result: $result")
        } catch (e: Exception) {
            throw IllegalArgumentException("Failed to parse S-expression: ${e.message}", e)
        }
}
