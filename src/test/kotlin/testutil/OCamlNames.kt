package testutil

/** OCaml's infix operators whose names are words. */
private val wordOperators = setOf("mod", "land", "lor", "lxor", "lsl", "lsr", "asr")

/**
 * The name the value [name] goes by in examples, type assignments and signatures, however they
 * space it. Operators, and any other names without letters, are put in parentheses without spaces:
 * `(+)`, `(*)`, `(mod)`. `OCamlSource` spaces the ones OCaml would read as a comment when it writes
 * examples as OCaml.
 */
fun ocamlName(name: String): String = if (name !in wordOperators && name.any { it.isLetter() }) name else "($name)"
