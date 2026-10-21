package testutil

import query.App
import query.Example
import query.Examples
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

/** A labelled or optional argument, like `~f:succ` or `?x`, unlike the operators `~-` and `~-.`. */
private fun isLabel(atom: String) =
    atom.length > 1 && atom[0] in "~?" && (atom[1].isLetter() || atom[1] == '_')

fun SExpr.toExample(): Example =
    when (this) {
        is SExpr.Atm -> {
            require(!isLabel(value)) {
                "Examples cannot pass labelled or optional arguments, as in $value: pass a labelled " +
                    "argument positionally, in the order its signature declares it, and leave out optional ones"
            }
            Name(ocamlName(value))
        }
        is SExpr.Lst -> {
            require(this.elements.isNotEmpty())
            val apps = this.elements.map { it.toExample() }
            fun leftAssocApp(apps: List<Example>): Example =
                if (apps.size == 1) apps[0] else App(leftAssocApp(apps.dropLast(1)), apps.last())
            leftAssocApp(apps)
        }
    }

fun unsignedExample(s: String) = parseSExpr(s).toExample()

fun signedExample(s: String) = parseSExpr(s).toSignedExample().second
