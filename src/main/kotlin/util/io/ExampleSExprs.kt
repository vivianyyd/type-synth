package util.io

import query.*
import util.io.generatedexamples.readExamples

fun signedSexpsFromExamples(exs: Collection<Example>, pos: Boolean): Collection<SExpr> =
    exs.map { SExpr.Lst(listOf(SExpr.Atm(if (pos) "+" else "-"), it.flatten().toSExpr())) }

private fun FlatApp.toSExpr(): SExpr =
    if (this.args.isEmpty()) SExpr.Atm(name)
    else SExpr.Lst(listOf(SExpr.Atm(name)) + args.map { it.toSExpr() })

/**
 * Parses test where [name] is the extensionless name of a file containing a ground truth type
 * assignment as SExps in the first line followed by SExps of examples labeled with +/-.
 */
fun parseTest(name: String): Query {
    val exs = readExamples(name)
    return Query(
        signedExamplesFromStrings(exs.second.filter { it.isNotBlank() }),
        oracleFromAssignment(exs.first)
    )
}

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
            val name = this.value
            val parenName =
                if (name == "*") "( * )" else if (name.all { !it.isLetter() }) "($name)" else name
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
