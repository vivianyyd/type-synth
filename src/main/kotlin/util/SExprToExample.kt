package util

fun parseExamples(sexps: Collection<String>): Query = examplesFromSexps(sexps.map{SExprParser(it).parse()})

private fun examplesFromSexps(sexps: Collection<SExpr>): Query {
    val exsWithNames = sexps.map { it.toExample() }
    val exs = exsWithNames.map { Pair(it.second, it.first) }
    val names = exsWithNames.map { it.third }.fold(setOf<String>()) { a, b -> a.union(b) }
    val (pos, neg) = splitExamples(exs)
    return Query(pos, neg, names.toList())
}

/**
 * Posex, negex, names mentioned
 */
private fun splitExamples(exs: List<Pair<Application, Boolean>>): Pair<List<Application>, List<Application>> {
    val (pos, neg) = exs.partition { (_, sign) -> sign }
    return Pair(
        pos.map { (ex, _) -> ex },
        neg.map { (ex, _) -> ex },
    )
}

private fun SExpr.toExample(): Triple<Boolean, Application, Set<String>> = when (this) {
    is SExpr.Atm -> {
        throw Exception("Not an example")
    }
    is SExpr.Lst -> {
        assert(this.elements.size == 2)
        assert(this.elements[0] is SExpr.Atm)
        val sign = (this.elements[0] as SExpr.Atm).value
        assert(sign == "+" || sign == "-")
        val (ex, names) = this.elements[1].toApplication()
        Triple(sign == "+", ex, names)
    }
}

private fun SExpr.toApplication(): Pair<Application, Set<String>> = when (this) {
    is SExpr.Atm -> {
        Pair(Application(this.value), setOf(this.value))
    }
    is SExpr.Lst -> {
        assert(this.elements.isNotEmpty())
        val (apps, names) = this.elements.map { it.toApplication() }.unzip()
        if (elements[0] is SExpr.Atm) Pair(
            Application((elements[0] as SExpr.Atm).value, apps.drop(1)),
            names.fold(setOf()) { a, n -> a.union(n) })
        else
            TODO("Not yet implemented: Parsing application where the function is the result of an application")  // Pair(Application(apps[0]))
    }
}

fun parseApp(s: String) = SExprParser(s).parse().toApplication().first