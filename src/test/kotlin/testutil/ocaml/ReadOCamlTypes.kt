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

    /**
     * Arrows are right-associative and have the lowest precedence: `a -> b -> c` parses as
     * `a -> (b -> c)`.
     */
    private fun parseArrow(tokens: List<String>, ctx: VariableContext): Pair<Type, List<String>> {
        val (lhs, rest) = parseTuple(tokens, ctx)
        return if (rest.firstOrNull() == "->") {
            val (rhs, next) = parseArrow(rest.drop(1), ctx)
            Arrow(lhs, rhs) to next
        } else {
            lhs to rest
        }
    }

    /**
     * Tuple types bind tighter than arrows but looser than constructor application:
     * `'a * 'b list` parses as `'a * ('b list)`. An n-tuple becomes a [NamedLabel] with n
     * parameters, using an arity-tagged constructor so that pairs, triples, etc. are distinct
     * labels (mirroring how `int`/`bool` become zero-parameter labels).
     */
    private fun parseTuple(tokens: List<String>, ctx: VariableContext): Pair<Type, List<String>> {
        val (first, rest0) = parseApplication(tokens, ctx)
        if (rest0.firstOrNull() != "*") return first to rest0
        val components = mutableListOf(first)
        var rest = rest0
        while (rest.firstOrNull() == "*") {
            val (component, next) = parseApplication(rest.drop(1), ctx)
            components.add(component)
            rest = next
        }
        return NamedLabel(constructorId("*${components.size}"), components) to rest
    }

    /**
     * OCaml type-constructor application is postfix and left-associative: `'a list` applies `list`
     * to `'a`, and `'a list list` is `list (list 'a)`. Multi-parameter constructors are written
     * with their arguments parenthesized and comma-separated, e.g. `('b, 'c) Either.t`; those are
     * handled in [parseAtom].
     */
    private fun parseApplication(
        tokens: List<String>,
        ctx: VariableContext
    ): Pair<Type, List<String>> {
        var (base, rest) = parseAtom(tokens, ctx)
        while (rest.isNotEmpty() && isConstructorName(rest[0])) {
            base = NamedLabel(constructorId(rest[0]), listOf(base))
            rest = rest.drop(1)
        }
        return base to rest
    }

    private fun parseAtom(tokens: List<String>, ctx: VariableContext): Pair<Type, List<String>> {
        require(tokens.isNotEmpty()) { "Unexpected end of input" }
        val head = tokens.first()
        return when {
            head.startsWith("'") -> {
                Variable(ctx.variableId(head)) to tokens.drop(1)
            }
            head == "(" -> parseParenthesized(tokens.drop(1), ctx)
            isConstructorName(head) -> {
                NamedLabel(constructorId(head), emptyList()) to tokens.drop(1)
            }
            else -> error("Unexpected token '$head'")
        }
    }

    /**
     * Parses the remainder after a `(`. A plain `( typexpr )` is a grouping, while a comma-separated
     * `( t1 , t2 , ... ) Constr` is a multi-parameter constructor application whose arguments precede
     * the constructor name.
     */
    private fun parseParenthesized(
        tokens: List<String>,
        ctx: VariableContext
    ): Pair<Type, List<String>> {
        val (first, rest0) = parseArrow(tokens, ctx)
        if (rest0.firstOrNull() == ",") {
            val args = mutableListOf(first)
            var rest = rest0
            while (rest.firstOrNull() == ",") {
                val (arg, next) = parseArrow(rest.drop(1), ctx)
                args.add(arg)
                rest = next
            }
            require(rest.firstOrNull() == ")") { "Expected closing parenthesis" }
            rest = rest.drop(1)
            val ctor = rest.firstOrNull()
            require(ctor != null && isConstructorName(ctor)) {
                "Expected type constructor after parenthesized arguments, got $ctor"
            }
            return NamedLabel(constructorId(ctor), args) to rest.drop(1)
        }
        require(rest0.firstOrNull() == ")") { "Expected closing parenthesis" }
        return first to rest0.drop(1)
    }

    private fun constructorId(name: String): Int =
        constructorIds.getOrPut(name) { nextConstructorId++ }

    private fun tokenize(expr: String): List<String> =
        expr
            .replace("(", " ( ")
            .replace(")", " ) ")
            .replace("->", " -> ")
            .replace("*", " * ")
            .replace(",", " , ")
            .split(Regex("\\s+"))
            .filter { it.isNotEmpty() }

    /**
     * A type constructor name is an identifier (possibly module-qualified, e.g. `Either.t`). It is
     * distinguished from the punctuation tokens produced by [tokenize] and from type variables.
     */
    private fun isConstructorName(token: String): Boolean =
        token.firstOrNull()?.isLetter() == true

    private data class VariableContext(
        val ids: MutableMap<String, Int> = mutableMapOf(),
        var nextId: Int = 0
    ) {
        fun variableId(name: String): Int = ids.getOrPut(name) { nextId++ }
    }
}
