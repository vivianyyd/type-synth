package parsing

import enumgen.*

/**
 * posexs, negexs, names mentioned
 */
fun examples(sexps: List<SExpr>): Triple<List<Application>, List<Application>, Set<String>> {
    val exs = sexps.map { it.toExample() }
    val (pos, neg) = exs.partition { (sign, _, _) -> sign }
    return Triple(
        pos.map { (_, ex, _) -> ex },
        neg.map { (_, ex, _) -> ex },
        exs.map { it.third }.fold(setOf()) { a, b -> a.union(b) })
}

fun SExpr.toExample(): Triple<Boolean, Application, Set<String>> = when (this) {
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

fun SExpr.toApplication(): Pair<Application, Set<String>> = when (this) {
    is SExpr.Atm -> {
        Pair(Application(this.value, null), setOf(this.value))
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

/*
(+ (cons a b))
(+ (cons a (cons b c))))
(+ []i)
(+ 0)
 */
