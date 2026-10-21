package testutil

/** OCaml's infix operators whose names are words. */
private val wordOperators = setOf("mod", "land", "lor", "lxor", "lsl", "lsr", "asr")

/**
 * How the value named [name] is written in OCaml source, which is also the name it goes by in
 * examples and type assignments. Operators, and any other names without letters, are put in
 * parentheses. An operator that begins or ends with `*` gets spaces inside them, or `(*.)` would
 * open a comment and `(**)` would be an empty one; `mod` gets them too, as the signatures spell it.
 */
fun ocamlName(name: String): String =
    when {
        name !in wordOperators && name.any { it.isLetter() } -> name
        name.startsWith("*") || name.endsWith("*") || name == "mod" -> "( $name )"
        else -> "($name)"
    }
