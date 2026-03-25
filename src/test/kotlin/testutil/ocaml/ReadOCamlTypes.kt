package testutil.ocaml

import oneast.Arrow
import oneast.NamedLabel
import oneast.Type
import oneast.Variable

/** Parses a single OCaml-style type expression into the custom [Type] AST. */
fun parseTypeExpression(source: String): Type =
    TypeParsingSession().parse(normalizeTypeLine(source))

/**
 * Parses newline-separated type expressions, sharing constructor labels across all parsed types.
 */
fun parseTypeExpressions(source: String): List<Type> {
    val session = TypeParsingSession()
    return source
        .lineSequence()
        .map(::normalizeTypeLine)
        .filter { it.isNotEmpty() }
        .map { session.parse(it) }
        .toList()
}

fun main() {
    val types =
        """
        'a list -> 'b list -> int
        'a -> 'a
        """
            .trimIndent()
    println(parseTypeExpressions(types))
}

private fun normalizeTypeLine(raw: String): String {
    var trimmed = raw.trim()
    while (trimmed.endsWith(";")) {
        trimmed = trimmed.dropLast(1).trimEnd()
    }
    return trimmed
}

private class TypeParsingSession {
    private val constructorLabels = linkedMapOf<String, Int>()

    fun parse(source: String): Type = TypeExpressionParser(source, constructorLabels).parse()
}

private class TypeExpressionParser(
    source: String,
    private val constructorLabels: MutableMap<String, Int>
) {
    private val tokens = Lexer(source).tokenize()
    private var index = 0
    private val typeVariables = linkedMapOf<String, Int>()

    fun parse(): Type {
        val type = parseType()
        require(isAtEnd()) { "Unexpected tokens after type expression" }
        return type
    }

    private fun parseType(): Type = parseArrowType()

    private fun parseArrowType(): Type {
        val left = parseApplicationType()
        return if (match<Token.Arrow>()) Arrow(left, parseArrowType()) else left
    }

    private fun parseApplicationType(): Type {
        var current = parseAtomicType()
        while (true) {
            current =
                when (val next = peek()) {
                    is Token.Identifier -> {
                        advance()
                        constructorType(next.value, listOf(current))
                    }
                    else -> return current
                }
        }
    }

    private fun parseAtomicType(): Type =
        when (val token = advance()) {
            is Token.TypeVariable -> Variable(typeVariableId(token.name))
            is Token.Identifier -> constructorType(token.value, emptyList())
            Token.LParen -> parseParenthesized()
            else -> error("Unexpected token $token while parsing type")
        }

    private fun parseParenthesized(): Type {
        val inner = parseType()
        expect(Token.RParen, "Missing closing ')'")
        return inner
    }

    private fun constructorType(name: String, params: List<Type>): Type {
        val id = constructorLabels.getOrPut(name) { constructorLabels.size }
        return NamedLabel(id, params)
    }

    private fun typeVariableId(raw: String): Int =
        typeVariables.getOrPut(raw) { typeVariables.size }

    private inline fun <reified T : Token> match(): Boolean =
        if (peek() is T) {
            advance()
            true
        } else {
            false
        }

    private fun expect(token: Token, message: String) {
        if (advance() != token) error(message)
    }

    private fun isAtEnd(): Boolean = peek() == Token.EOF

    private fun peek(): Token = tokens.getOrNull(index) ?: Token.EOF

    private fun advance(): Token = tokens.getOrNull(index++) ?: Token.EOF
}

private class Lexer(private val input: String) {
    private var index = 0

    fun tokenize(): List<Token> {
        val tokens = mutableListOf<Token>()
        while (index < input.length) {
            when (val ch = input[index]) {
                ' ',
                '\t',
                '\r',
                '\n' -> index++
                '(' -> {
                    tokens += Token.LParen
                    index++
                }
                ')' -> {
                    tokens += Token.RParen
                    index++
                }
                '-' -> {
                    if (peekChar() == '>') {
                        tokens += Token.Arrow
                        index += 2
                    } else error("Unexpected '-' at $index")
                }
                '\'' -> tokens += readTypeVariable()
                else -> {
                    if (ch.isLetter()) {
                        tokens += readIdentifier()
                    } else error("Unexpected character '$ch' at $index")
                }
            }
        }
        tokens += Token.EOF
        return tokens
    }

    private fun readIdentifier(): Token.Identifier {
        val start = index
        while (index < input.length && (input[index].isLetterOrDigit() || input[index] == '_')) {
            index++
        }
        val word = input.substring(start, index)
        return Token.Identifier(word)
    }

    private fun readTypeVariable(): Token.TypeVariable {
        index++ // skip apostrophe
        val start = index
        require(index < input.length && input[index].isLetter()) { "Empty type variable" }
        while (index < input.length && (input[index].isLetterOrDigit() || input[index] == '_')) {
            index++
        }
        return Token.TypeVariable(input.substring(start, index))
    }

    private fun peekChar(): Char? = input.getOrNull(index + 1)
}

private sealed interface Token {
    object Arrow : Token

    object LParen : Token

    object RParen : Token

    object EOF : Token

    data class Identifier(val value: String) : Token

    data class TypeVariable(val name: String) : Token
}

/**
 * Parses OCaml-style value signatures (e.g. `val foo : 'a list -> int`) into the repository's
 * [Type] AST. Type variables are assigned stable numeric IDs within each signature, while
 * constructors share IDs across all parsed signatures so that every constructor name maps to a
 * unique [NamedLabel] label.
 */
class OcamlTypeParser {
    private val constructorIds = mutableMapOf<String, Int>()
    private var nextConstructorId = 0

    /**
     * Parses one or more signatures (separated by newlines) into a map from value names to [Type]s.
     */
    fun parseSignatures(block: String): Map<String, Type> {
        val result = LinkedHashMap<String, Type>()
        block
            .lineSequence()
            .map { it.trim() }
            .filter { it.isNotEmpty() && !it.startsWith("//") }
            .forEach { line ->
                val (name, type) = parseSignatureLine(line)
                result[name] = type
            }
        return result
    }

    /** Convenience wrapper when only a single signature string is provided. */
    fun parseSignature(signature: String): Map<String, Type> = parseSignatures(signature)

    private fun parseSignatureLine(line: String): Pair<String, Type> {
        val normalized = normalizeLine(line)
        val colonIndex = normalized.indexOf(':')
        require(colonIndex >= 0) { "Signature must contain ':' : $line" }
        val name = normalized.substring(0, colonIndex).trim()
        val typePart = normalized.substring(colonIndex + 1).trim()

        val tokens = tokenize(typePart)
        val variableContext = VariableContext()
        val (type, remaining) = parseArrow(tokens, variableContext)
        require(remaining.isEmpty()) { "Unparsed tokens: $remaining" }
        return name to type
    }

    private fun normalizeLine(line: String): String {
        var trimmed = line.trim()
        while (trimmed.endsWith(";")) {
            trimmed = trimmed.dropLast(1).trimEnd()
        }
        if (trimmed.startsWith("val ")) {
            trimmed = trimmed.removePrefix("val ").trimStart()
        }
        return trimmed
    }

    private fun parseArrow(tokens: List<String>, ctx: VariableContext): Pair<Type, List<String>> {
        var (lhs, rest) = parseApplication(tokens, ctx)
        while (rest.firstOrNull() == "->") {
            val (rhs, next) = parseArrow(rest.drop(1), ctx)
            lhs = Arrow(lhs, rhs)
            rest = next
        }
        return lhs to rest
    }

    private fun parseApplication(
        tokens: List<String>,
        ctx: VariableContext
    ): Pair<Type, List<String>> {
        var (current, rest) = parseAtom(tokens, ctx)
        // OCaml uses postfix type application: 'a list means list('a), not 'a applied to list.
        while (rest.isNotEmpty() && rest[0].firstOrNull()?.isLetter() == true) {
            val constructorName = rest[0]
            rest = rest.drop(1)
            current = NamedLabel(constructorId(constructorName), listOf(current))
        }
        return current to rest
    }

    private fun parseAtom(tokens: List<String>, ctx: VariableContext): Pair<Type, List<String>> {
        require(tokens.isNotEmpty()) { "Unexpected end of input" }
        val head = tokens.first()
        return when {
            head.startsWith("'") -> {
                Variable(ctx.variableId(head)) to tokens.drop(1)
            }
            head == "(" -> {
                val (inner, rest) = parseArrow(tokens.drop(1), ctx)
                require(rest.firstOrNull() == ")") { "Expected closing parenthesis" }
                inner to rest.drop(1)
            }
            else -> {
                NamedLabel(constructorId(head), emptyList()) to tokens.drop(1)
            }
        }
    }

    private fun constructorId(name: String): Int =
        constructorIds.getOrPut(name) { nextConstructorId++ }

    private fun tokenize(expr: String): List<String> =
        expr
            .replace("(", " ( ")
            .replace(")", " ) ")
            .replace("->", " -> ")
            .split(Regex("\\s+"))
            .filter { it.isNotEmpty() }

    private data class VariableContext(
        val ids: MutableMap<String, Int> = mutableMapOf(),
        var nextId: Int = 0
    ) {
        fun variableId(name: String): Int = ids.getOrPut(name) { nextId++ }
    }
}
