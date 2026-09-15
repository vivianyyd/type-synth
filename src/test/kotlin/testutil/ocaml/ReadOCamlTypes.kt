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
    fun parseSignatures(block: String): Map<String, Type> {
        val result = LinkedHashMap<String, Type>()
        block
            .lineSequence()
            .map { it.substringBefore("//").trim() }
            .filter { it.isNotEmpty() }
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
        // An operator name can itself contain ':', e.g. `(:=)`, so the separator comes after it.
        val nameEnd = if (normalized.startsWith("(")) normalized.indexOf(')') else 0
        val colonIndex = normalized.indexOf(':', nameEnd)
        require(colonIndex >= 0) { "Signature must contain ':' : $line" }
        val name = normalized.substring(0, colonIndex).trim()
        val typePart = normalized.substring(colonIndex + 1).trim()

        val tokens = tokenize(typePart)
        val variableContext = VariableContext()
        val (type, remaining) = parseAlias(tokens, variableContext)
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
     * `t as 'a` names `t`, so later occurrences of `'a` stand for `t`. It has the lowest
     * precedence: `a -> b as 'c` names the whole arrow type.
     */
    private fun parseAlias(tokens: List<String>, ctx: VariableContext): Pair<Type, List<String>> {
        val (type, rest) = parseArrow(tokens, ctx)
        if (rest.firstOrNull() != "as") return type to rest
        val variable = rest.getOrNull(1)
        require(variable != null && variable.startsWith("'")) {
            "Expected type variable after 'as', got $variable"
        }
        require(variable !in ctx.ids) { "Type variable $variable is used before 'as' names it" }
        ctx.aliases[variable] = type
        return type to rest.drop(2)
    }

    /**
     * Arrows are right-associative and bind tighter only than `as`: `a -> b -> c` parses as
     * `a -> (b -> c)`. Our types have no argument labels, so labelled and optional arguments drop
     * their label: `label:a -> b` and `?label:a -> b` both parse as `a -> b`.
     */
    private fun parseArrow(tokens: List<String>, ctx: VariableContext): Pair<Type, List<String>> {
        val unlabelled = if (tokens.getOrNull(1) == ":") tokens.drop(2) else tokens
        val (lhs, rest) = parseTuple(unlabelled, ctx)
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
                (ctx.aliases[head] ?: Variable(ctx.variableId(head))) to tokens.drop(1)
            }
            head == "(" -> parseParenthesized(tokens.drop(1), ctx)
            // Our types have no objects, so the open object type `<..>` is a constant like `int`.
            isConstructorName(head) || head == "<..>" -> {
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
        val (first, rest0) = parseAlias(tokens, ctx)
        if (rest0.firstOrNull() == ",") {
            val args = mutableListOf(first)
            var rest = rest0
            while (rest.firstOrNull() == ",") {
                val (arg, next) = parseAlias(rest.drop(1), ctx)
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
            .replace(Regex("<\\s*\\.\\.\\s*>"), " <..> ")
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
     * distinguished from the punctuation tokens produced by [tokenize], from type variables, and
     * from the keyword `as`.
     */
    private fun isConstructorName(token: String): Boolean =
        token.firstOrNull()?.isLetter() == true && token != "as"

    private data class VariableContext(
        val ids: MutableMap<String, Int> = mutableMapOf(),
        var nextId: Int = 0,
        /** Type variables named by `as`, mapped to the type they stand for. */
        val aliases: MutableMap<String, Type> = mutableMapOf()
    ) {
        fun variableId(name: String): Int = ids.getOrPut(name) { nextId++ }
    }
}
