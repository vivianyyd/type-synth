package testutil.ocaml

import query.App
import query.Example
import query.Name

/**
 * How examples are written as OCaml source, for the ways to ask OCaml about them ([OCamlGroundTruth]).
 *
 * @param labels The labels of each value's parameters, as [withLabels] takes them.
 */
data class OCamlSource(val labels: Map<String, List<String?>> = emptyMap()) {
    /** [example] as OCaml source. */
    fun of(example: Example): String = withLabels(withDummies(example), labels).toString()
}

// The rewrites below make examples only for printing as OCaml source. In them, a Name can be any
// OCaml text, like `()` or `~default:(1)`.

/** OCaml values that the examples name by their type, as `Num` for an int. */
private val dummies =
    mapOf("Num" to "1", "Str" to "\"s\"", "Char" to "'a'", "Flt" to "1.", "Nil" to "[]", "Unit" to "()")

/**
 * [name] spaced, as `( * )`, if it is an operator that starts or ends with `*`, since in OCaml `(*`
 * opens a comment and `*)` closes one.
 */
private fun spacedOperator(name: String): String =
    if (name.startsWith("(*") || name.endsWith("*)")) "( ${name.removeSurrounding("(", ")")} )" else name

/**
 * [e] with each name in [dummies] replaced by its value, and each operator spaced as
 * [spacedOperator] spaces it.
 */
private fun withDummies(e: Example): Example =
    when (e) {
        is Name -> Name(dummies[e.name] ?: spacedOperator(e.name))
        is App -> App(withDummies(e.fn), withDummies(e.arg))
    }

/**
 * [example] with each argument to a labelled parameter written with its label: with
 * `val value : 'a option -> default:'a -> 'a`, `Option.value o d` becomes
 * `Option.value o ~default:(d)`. Our types treat labelled parameters as positional, in the order
 * they are declared, so this is where the label goes.
 *
 * Only a value applied directly is labelled, not one passed as an argument. [labels] has, for each
 * value with labelled parameters, the label of each parameter, or null for an unlabelled one.
 */
fun withLabels(example: Example, labels: Map<String, List<String?>>): Example =
    when (example) {
        is Name -> example
        is App -> {
            val spine = example.flatten()
            val ofHead = labels[spine.name]
            if (ofHead == null) App(withLabels(example.fn, labels), withLabels(example.arg, labels))
            else
                spine.args.withIndex().fold(Name(spine.name) as Example) { fn, (i, arg) ->
                    val labelled = withLabels(arg.unflatten(), labels)
                    App(fn, ofHead.getOrNull(i)?.let { Name("~$it:($labelled)") } ?: labelled)
                }
        }
    }
