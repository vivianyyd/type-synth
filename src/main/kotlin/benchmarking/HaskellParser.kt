package benchmarking

import oneast.Arrow
import oneast.NamedLabel
import oneast.Type
import oneast.Variable

fun parseHaskellTypes(signatures: List<String>): List<Pair<Type, String>> {
    val context = ParseContext()
    return signatures.map { parseTypeSignature(it, context) }
}

/** Parse a single Haskell type signature into a oneast.Type. */
fun parseTypeSignature(signature: String): Pair<Type, String> =
    parseTypeSignature(signature, ParseContext())

/** Parse using a shared context so label/variable IDs stay consistent across signatures. */
fun parseTypeSignature(signature: String, context: ParseContext): Pair<Type, String> {
    val typePart = signature.substringAfter("::").trim()
    val tokens = tokenize(typePart)
    val parser = Parser(tokens, context)
    return parser.parseType() to signature.substringBefore("::").trim()
}

/** Tracks label/variable IDs while parsing multiple signatures in the same context. */
class ParseContext(
    val labelIds: MutableMap<String, Int> = mutableMapOf(),
    val variableIds: MutableMap<String, Int> = mutableMapOf(),
    val variableNames: MutableMap<Int, String> = mutableMapOf(),
    val variableLabelIds: MutableMap<String, Int> = mutableMapOf(),
    var nextId: Int = 0
)

sealed class Token {
    data class Ident(val value: String) : Token()

    object Arrow : Token() // ->

    object LParen : Token() // (

    object RParen : Token() // )

    object LBracket : Token() // [

    object RBracket : Token() // ]

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

private class Parser(private val tokens: List<Token>, private val context: ParseContext) {
    private var index = 0

    private fun peek(): Token? = tokens.getOrNull(index)

    private fun consume(): Token = tokens[index++]

    fun parseType(): Type = parseArrowType()

    private fun parseArrowType(): Type {
        var left = parseApplicationType()
        while (peek() == Token.Arrow) {
            consume() // consume ->
            val right = parseArrowType() // right-associative
            left = Arrow(left, right)
        }
        return left
    }

    private fun parseApplicationType(): Type {
        val parts = mutableListOf<Type>()
        while (true) {
            val part =
                when (val token = peek()) {
                    is Token.Ident -> {
                        consume()
                        if (token.value.first().isUpperCase()) {
                            // Capitalized word — treat as LabelNode with no parameters
                            NamedLabel(labelId(token.value), listOf())
                        } else {
                            // Lowercase — treat as variable
                            Variable(variableId(token.value))
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
                            2 -> NamedLabel(labelId("Pair"), elements)
                            else -> error("Tuples with arity ${elements.size} are not supported")
                        }
                    }
                    Token.LBracket -> {
                        consume()
                        val inner = parseType()
                        expect<Token.RBracket>("Expected ']'")
                        NamedLabel(labelId("List"), listOf(inner))
                    }
                    else -> break
                }
            parts.add(part)
        }

        return when {
            parts.isEmpty() -> throw IllegalStateException("Expected a type")
            parts.size == 1 -> parts[0]
            parts[0] is Variable -> {
                val head = parts[0] as Variable
                NamedLabel(variableApplicationLabelId(head), parts.drop(1))
            }
            parts[0] is NamedLabel -> {
                val head = parts[0] as NamedLabel
                NamedLabel(head.label, head.params + parts.drop(1))
            }
            else -> throw IllegalStateException("Invalid label node")
        }
    }

    private fun variableId(name: String): Int =
        context.variableIds.getOrPut(name) {
            val id = context.nextId++
            context.variableNames[id] = name
            id
        }

    private fun labelId(name: String): Int =
        context.labelIds.getOrPut(name) {
            val id = context.nextId++
            id
        }

    private fun variableApplicationLabelId(variable: Variable): Int {
        val name =
            requireNotNull(context.variableNames[variable.v]) { "Missing variable ${variable.v}" }
        return context.variableLabelIds.getOrPut(name) {
            val id = context.nextId++
            id
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
    val inputs =
        listOf(
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
