package testutil.ocaml

import query.App
import query.Example
import query.Name

/** How examples are written as OCaml source, for the ways to ask OCaml about them ([OCamlGroundTruth]). */
class OCamlSource {
    /** [example] as OCaml source. */
    fun of(example: Example): String = withDummies(example).toString()
}

// The rewrites below make examples only for printing as OCaml source. In them, a Name can be any
// OCaml text, like `()`.

/** OCaml values that the examples name by their type, as `Num` for an int. */
private val dummies =
    mapOf("Num" to "1", "Str" to "\"s\"", "Char" to "'a'", "Flt" to "1.", "Nil" to "[]", "Unit" to "()")

/** [e] with each name in [dummies] replaced by its value. */
private fun withDummies(e: Example): Example =
    when (e) {
        is Name -> dummies[e.name]?.let(::Name) ?: e
        is App -> App(withDummies(e.fn), withDummies(e.arg))
    }
