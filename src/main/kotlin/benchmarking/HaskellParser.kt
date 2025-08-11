package benchmarking

import types.Function
import types.LabelNode
import types.Type
import types.Variable

fun parseHaskellTypes(signatures: List<String>): List<Pair<Type, String>> = signatures.map { parseTypeSignature(it) }

fun parseTypeSignature(signature: String): Pair<Type, String> {
    val typePart = signature.substringAfter("::").trim()
    val tokens = tokenize(typePart)
    val parser = Parser(tokens)
    return parser.parseType() to signature.substringBefore("::").trim()
}

sealed class Token {
    data class Ident(val value: String) : Token()
    object Arrow : Token()              // ->
    object LParen : Token()            // (
    object RParen : Token()            // )
    object LBracket : Token()  // [
    object RBracket : Token()  // ]
    object Comma : Token()
}

fun tokenize(input: String): List<Token> {
    val tokens = mutableListOf<Token>()
    var i = 0

    while (i < input.length) {
        when {
            input.startsWith("->", i) -> {
                tokens.add(Token.Arrow)
                i += 2
            }
            input[i].isWhitespace() -> i++
            input[i] == '(' -> {
                tokens.add(Token.LParen)
                i++
            }
            input[i] == ')' -> {
                tokens.add(Token.RParen)
                i++
            }
            input[i] == '[' -> {
                tokens.add(Token.LBracket)
                i++
            }
            input[i] == ']' -> {
                tokens.add(Token.RBracket)
                i++
            }
            input[i] == ',' -> {
                tokens.add(Token.Comma)
                i++
            }
            else -> {
                val start = i
                while (i < input.length && (input[i].isLetterOrDigit() || input[i] == '_')) i++
                tokens.add(Token.Ident(input.substring(start, i)))
            }
        }
    }

    return tokens
}

class Parser(private val tokens: List<Token>) {
    private var index = 0

    private fun peek(): Token? = tokens.getOrNull(index)
    private fun consume(): Token = tokens[index++]

    fun parseType(): Type = parseArrowType()

    private fun parseArrowType(): Type {
        var left = parseApplicationType()
        while (peek() == Token.Arrow) {
            consume() // consume ->
            val right = parseArrowType() // right-associative
            left = Function(left, right)
        }
        return left
    }

    private fun parseApplicationType(): Type {
        val parts = mutableListOf<Type>()
        while (true) {
            val part = when (val token = peek()) {
                is Token.Ident -> {
                    consume()
                    if (token.value.first().isUpperCase()) {
                        // Capitalized word — treat as LabelNode with no parameters
                        LabelNode(token.value, listOf())
                    } else {
                        // Lowercase — treat as variable
                        Variable(token.value)
                    }
                }
                Token.LParen -> {
                    consume()
                    val elements = mutableListOf<Type>()
                    elements.add(parseType())

                    while (peek() == Token.Comma) {
                        consume() // consume comma
                        elements.add(parseType())
                    }

                    expect<Token.RParen>("Expected ')' to close tuple or group")

                    when (elements.size) {
                        1 -> elements[0] // parenthesized type
                        2 -> LabelNode("Pair", elements)
                        else -> error("Tuples with arity ${elements.size} are not supported")
                    }
                }
                Token.LBracket -> {
                    consume()
                    val inner = parseType()
                    expect<Token.RBracket>("Expected ']'")
                    LabelNode("List", listOf(inner))
                }
                else -> break
            }
            parts.add(part)
        }

        return when {
            parts.isEmpty() -> throw IllegalStateException("Expected a type")
            parts.size == 1 -> parts[0]
            parts[0] is Variable -> {
                val label = (parts[0] as Variable).id
                LabelNode(label, parts.drop(1))
            }
            parts[0] is LabelNode -> {
                val head = parts[0] as LabelNode
                LabelNode(head.label, head.params + parts.drop(1))
            }
            else -> throw IllegalStateException("Invalid label node")
        }
    }

    private inline fun <reified T : Token> expect(message: String): T {
        val token = consume()
        if (token !is T) throw IllegalArgumentException(message)
        return token
    }
}

fun main() {
//    val inputs = listOf(
//        "either :: (a -> c) -> (b -> c) -> Either a b -> c",
//        "f :: a -> b -> c",
//        "g :: Maybe (a -> b) -> c",
//        "f :: [a] -> b",
//        "f :: (a, b) -> c"
//    )
    val inputs = listOf(
        "either :: (a -> c) -> (b -> c) -> Either a b -> c",
        "lefts :: [Either a b] -> [a]",
        "rights :: [Either a b] -> [b]",
        "isLeft :: Either a b -> Bool",
        "isRight :: Either a b -> Bool",
        "fromLeft :: a -> Either a b -> a",
        "fromRight :: b -> Either a b -> b",
        "partitionEithers :: [Either a b] -> ([a], [b])"
    )

    for (input in inputs) {
        val parsed = parseTypeSignature(input)
        println(parsed)
    }
}
