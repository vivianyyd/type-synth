package util

fun parseNewExamples(sexps: Collection<String>): NewQuery = examplesFromSexps(sexps.map { SExprParser(it).parse() })

private fun examplesFromSexps(sexps: Collection<SExpr>): NewQuery {
    val exsWithNames = sexps.map { it.toSignedExample() }
    val exs = exsWithNames.map { Pair(it.second, it.first) }
    val names = exsWithNames.map { it.third }.fold(setOf<String>()) { a, b -> a.union(b) }
    val (pos, neg) = splitNewExamples(exs)
    return NewQuery(pos, neg, names.toList())
}

/**
 * Posex, negex, names mentioned
 */
private fun splitNewExamples(exs: List<Pair<Example, Boolean>>): Pair<List<Example>, List<Example>> {
    val (pos, neg) = exs.partition { (_, sign) -> sign }
    return Pair(
        pos.map { (ex, _) -> ex },
        neg.map { (ex, _) -> ex },
    )
}

private fun SExpr.toSignedExample(): Triple<Boolean, Example, Set<String>> = when (this) {
    is SExpr.Atm -> {
        throw Exception("Not an example")
    }
    is SExpr.Lst -> {
        assert(this.elements.size == 2)
        assert(this.elements[0] is SExpr.Atm)
        val sign = (this.elements[0] as SExpr.Atm).value
        assert(sign == "+" || sign == "-")
        val (ex, names) = this.elements[1].toExpression()
        Triple(sign == "+", ex, names)
    }
}

private fun SExpr.toExpression(): Pair<Example, Set<String>> = when (this) {
    is SExpr.Atm -> {
        Pair(Name(this.value), setOf(this.value))
    }
    is SExpr.Lst -> {
        assert(this.elements.isNotEmpty())
        val (apps, names) = this.elements.map { it.toExpression() }.unzip()
        fun leftAssocApp(apps: List<Example>): Example =
            if (apps.size == 1) apps[0] else
                App(leftAssocApp(apps.dropLast(1)), apps.last())
        Pair(
            leftAssocApp(apps),
            names.fold(setOf()) { a, n -> a.union(n) }
        )
    }
}

fun parseNewApp(s: String) = SExprParser(s).parse().toExpression().first