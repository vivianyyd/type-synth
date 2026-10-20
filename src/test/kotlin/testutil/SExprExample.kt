package testutil

import query.App
import query.Example
import query.Examples
import query.Lam
import query.Let
import query.Name

/** Parses a collection of SExpr strings for *signed* examples (marked + or -). */
fun signedExamplesFromStrings(sexps: Collection<String>): Examples {
    val exsWithNames = sexps.map { parseSExpr(it).toSignedExample() }
    val exs = exsWithNames.map { Pair(it.second, it.first) }
    val (pos, neg) = exs.partition { (_, sign) -> sign }
    return Examples(
        pos.map { (ex, _) -> ex },
        neg.map { (ex, _) -> ex },
    )
}

private fun SExpr.toSignedExample(): Pair<Boolean, Example> =
    when (this) {
        is SExpr.Atm -> {
            throw Exception("Not an example")
        }
        is SExpr.Lst -> {
            require(this.elements.size == 2)
            require(this.elements[0] is SExpr.Atm)
            val sign = (this.elements[0] as SExpr.Atm).value
            require(sign == "+" || sign == "-")
            val ex = this.elements[1].toExample()
            Pair(sign == "+", ex)
        }
    }

/** Words that are syntax in examples, so never a name. */
private val keywords = setOf("fun", "->", "let", "in")

/**
 * Converts an S-expression to an example. A list is an application, `(f x y)`, unless it starts with
 * `fun` or `let`:
 * - `(fun x y -> body)` is a lambda with parameters x and y;
 * - `(let x = value in body)` is a let.
 * The value and the body are the rest of the list up to the next keyword, read as an application,
 * so `(fun x -> f x)` means `(fun x -> (f x))`. A lambda or let anywhere but at the start of a list
 * must be in a list of its own: `(f (fun x -> x))`.
 */
fun SExpr.toExample(): Example =
    when (this) {
        is SExpr.Atm -> {
            require(value !in keywords) { "Keyword '$value' is not at the start of a list" }
            require(value != "_") { "_ binds nothing, so it cannot be used" }
            // TODO ask LLM for cleaner implementation here
            val name = this.value
            val prefixAlphaNames = listOf(
                "land",
                "lor",
                "lxor",
                "lsl",
                "lsr",
                "asr"
            )
            val parenName =
                if (name == "*" || name == "mod") "( $name )" else if (name.all { !it.isLetter() } || name in prefixAlphaNames) "($name)" else name
            Name(parenName)
        }
        is SExpr.Lst ->
            when ((elements.firstOrNull() as? SExpr.Atm)?.value) {
                "fun" -> lamFromSExpr(elements)
                "let" -> letFromSExpr(elements)
                else -> application(elements)
            }
    }

private fun application(elements: List<SExpr>): Example {
    require(elements.isNotEmpty()) { "Empty application" }
    return elements.drop(1).fold(elements[0].toExample()) { fn, arg -> App(fn, arg.toExample()) }
}

/** What OCaml accepts as a variable name, apart from keywords. Capitalized names are constructors. */
private val lowercaseIdent = Regex("[a-z_][A-Za-z0-9_']*")

private val ocamlKeywords = setOf(
    "and", "as", "assert", "asr", "begin", "class", "constraint", "do", "done", "downto", "effect",
    "else", "end", "exception", "external", "false", "for", "fun", "function", "functor", "if", "in",
    "include", "inherit", "initializer", "land", "lazy", "let", "lor", "lsl", "lsr", "lxor", "match",
    "method", "mod", "module", "mutable", "new", "nonrec", "object", "of", "open", "or", "private",
    "rec", "sig", "struct", "then", "to", "true", "try", "type", "val", "virtual", "when", "while",
    "with"
)

/** The atom a binder binds, which must be a name OCaml can bind. `_` binds nothing. */
private fun binder(e: SExpr): String {
    require(e is SExpr.Atm && lowercaseIdent.matches(e.value) && e.value !in ocamlKeywords) {
        "Not a name that can be bound: $e"
    }
    return e.value
}

/** `(fun x y -> body)`. */
private fun lamFromSExpr(elements: List<SExpr>): Example {
    val arrow = elements.indexOfFirst { it is SExpr.Atm && it.value == "->" }
    require(arrow > 1) { "Expected (fun params -> body): ${SExpr.Lst(elements)}" }
    val params = elements.subList(1, arrow).map(::binder)
    val body = application(elements.subList(arrow + 1, elements.size))
    return params.foldRight(body) { param, b -> Lam(param, b) }
}

/** `(let x = value in body)`. */
private fun letFromSExpr(elements: List<SExpr>): Example {
    val inAt = elements.indexOfFirst { it is SExpr.Atm && it.value == "in" }
    require(elements.size > 3 && (elements[2] as? SExpr.Atm)?.value == "=" && inAt > 3) {
        "Expected (let x = value in body): ${SExpr.Lst(elements)}"
    }
    return Let(
        binder(elements[1]),
        application(elements.subList(3, inAt)),
        application(elements.subList(inAt + 1, elements.size))
    )
}

fun unsignedExample(s: String) = parseSExpr(s).toExample()

fun signedExample(s: String) = parseSExpr(s).toSignedExample().second
