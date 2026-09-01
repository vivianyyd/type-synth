package testutil

import java.io.StringReader
import testutil.parser.OCamlExprCupParser
import testutil.parser.OCamlExprLexer

fun parseOCamlExpr(s: String) = OCamlExprParser(s).parse()

sealed class OCamlExpr {
    data class Var(val name: String) : OCamlExpr()
    data class App(val func: OCamlExpr, val arg: OCamlExpr) : OCamlExpr()
    data class Lam(val params: List<String>, val body: OCamlExpr) : OCamlExpr()
}

private class OCamlExprParser(private val input: String) {
    fun parse(): OCamlExpr =
        try {
            val parser = OCamlExprCupParser(OCamlExprLexer(StringReader(input)))
            val result = parser.parse().value
            result as? OCamlExpr
                ?: throw IllegalStateException("Parser produced unexpected result: $result")
        } catch (e: Exception) {
            throw IllegalArgumentException("Failed to parse expression: ${e.message}", e)
        }
}
