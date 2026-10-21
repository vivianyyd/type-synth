package testutil.ocaml

import oneast.Arrow
import oneast.NamedLabel
import oneast.Type
import oneast.Variable

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
     * A `//` comment runs to the end of its line.
     */
    fun parseSignatures(block: String): Map<String, Type> =
        parseSignaturesWithLabels(block).mapValues { it.value.type }

    /** [parseSignatures], keeping each value's labels. */
    fun parseSignaturesWithLabels(block: String): Map<String, Signature> {
        val result = LinkedHashMap<String, Signature>()
        block
            .lineSequence()
            .map { it.substringBefore("//").trim() }
            .filter { it.isNotEmpty() }
            .forEach { line ->
                val (name, signature) = parseSignatureLine(line)
                result[name] = signature
            }
        return result
    }

    /** Convenience wrapper when only a single signature string is provided. */
    fun parseSignature(signature: String): Map<String, Type> = parseSignatures(signature)

    private fun parseSignatureLine(line: String): Pair<String, Signature> {
        val normalized = normalizeLine(line)
        // An operator name can itself contain ':', e.g. `(:=)`, so the separator comes after it.
        val nameEnd = if (normalized.startsWith("(")) normalized.indexOf(')') else 0
        val colonIndex = normalized.indexOf(':', nameEnd)
        require(colonIndex >= 0) { "Signature must contain ':' : $line" }
        val name = normalized.substring(0, colonIndex).trim()
        val typePart = normalized.substring(colonIndex + 1).trim()

        val tokens = tokenize(typePart)
        val variableContext = VariableContext()
        val labels = mutableListOf<String?>()
        val (type, remaining) = parseArrow(tokens, variableContext, labels)
        require(remaining.isEmpty()) { "Unparsed tokens: $remaining" }
        return name to Signature(type, labels)
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
     *
     * Our types have no labels. A labelled parameter is an ordinary one, so `label:a -> b` parses
     * as `a -> b`, and its label is added to [labels], which has an entry per parameter (null if
     * unlabelled). An optional parameter is left out, so `?label:a -> b` parses as `b`: OCaml gives
     * it its default when a later argument is passed. Only the outermost arrows have [labels].
     */
    private fun parseArrow(
        tokens: List<String>,
        ctx: VariableContext,
        labels: MutableList<String?>? = null
    ): Pair<Type, List<String>> {
        val label = if (tokens.getOrNull(1) == ":") tokens[0] else null
        val optional = label?.startsWith("?") == true
        val typeTokens = if (label == null) tokens else tokens.drop(2)
        // An optional parameter's type is read only to skip it, so its variables take up no ids
        val (lhs, rest) = parseTuple(typeTokens, if (optional) ctx.scratch() else ctx)
        if (rest.firstOrNull() != "->") {
            require(label == null) { "Parameter $label is not followed by '->'" }
            return lhs to rest
        }
        if (optional) return parseArrow(rest.drop(1), ctx, labels)
        labels?.add(label)
        val (rhs, next) = parseArrow(rest.drop(1), ctx, labels)
        return Arrow(lhs, rhs) to next
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
            .replace(":", " : ")
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

        /** A copy, to read a type in without changing this one. */
        fun scratch() = VariableContext(HashMap(ids), nextId)
    }
}

/**
 * A value's [type], and the label of each of its parameters, or null for an unlabelled one. An
 * optional parameter is in neither. See [OcamlTypeParser.parseSignaturesWithLabels].
 */
data class Signature(val type: Type, val labels: List<String?>)
