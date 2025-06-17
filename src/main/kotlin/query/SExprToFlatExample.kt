package query

import util.SExpr
import util.SExprParser

fun parseFlatExamples(sexps: Collection<String>): FlatQuery =
    flatExamplesFromSexps(sexps.map { SExprParser(it).parse() })

private fun flatExamplesFromSexps(sexps: Collection<SExpr>): FlatQuery {
    val exsWithNames = sexps.map { it.toFlatExample() }
    val exs = exsWithNames.map { Pair(it.second, it.first) }
    val names = exsWithNames.map { it.third }.fold(setOf<String>()) { a, b -> a.union(b) }
    val (pos, neg) = splitFlatExamples(exs)
    return FlatQuery(pos, neg, names.toList())
}

/**
 * Posex, negex, names mentioned
 */
private fun splitFlatExamples(exs: List<Pair<FlatApp, Boolean>>): Pair<List<FlatApp>, List<FlatApp>> {
    val (pos, neg) = exs.partition { (_, sign) -> sign }
    return Pair(
        pos.map { (ex, _) -> ex },
        neg.map { (ex, _) -> ex },
    )
}

private fun SExpr.toFlatExample(): Triple<Boolean, FlatApp, Set<String>> = when (this) {
    is SExpr.Atm -> {
        throw Exception("Not an example")
    }
    is SExpr.Lst -> {
        assert(this.elements.size == 2)
        assert(this.elements[0] is SExpr.Atm)
        val sign = (this.elements[0] as SExpr.Atm).value
        assert(sign == "+" || sign == "-")
        val (ex, names) = this.elements[1].toFlatApplication()
        Triple(sign == "+", ex, names)
    }
}

private fun SExpr.toFlatApplication(): Pair<FlatApp, Set<String>> = when (this) {
    is SExpr.Atm -> {
        Pair(FlatApp(this.value), setOf(this.value))
    }
    is SExpr.Lst -> {
        assert(this.elements.isNotEmpty())
        val (apps, names) = this.elements.map { it.toFlatApplication() }.unzip()
        if (elements[0] is SExpr.Atm) Pair(
            FlatApp((elements[0] as SExpr.Atm).value, apps.drop(1)),
            names.fold(setOf()) { a, n -> a.union(n) })
        else
            TODO("Not yet implemented: Parsing application where the function is the result of an application")  // Pair(Application(apps[0]))
    }
}

fun parseApp(s: String) = SExprParser(s).parse().toFlatApplication().first