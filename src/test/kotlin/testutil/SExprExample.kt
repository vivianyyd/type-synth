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

fun SExpr.toExample(): Example =
    when (this) {
        is SExpr.Atm -> {
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
