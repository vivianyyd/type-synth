package util.io

import products.types.toType
import query.*
import util.CheckingOracle
import util.QuerySpec
import util.io.generatedexamples.readExamples

fun sexpsFromExamples(exs: Collection<Example>, pos: Boolean): Collection<SExpr> =
    exs.map { SExpr.Lst(listOf(SExpr.Atm(if (pos) "+" else "-"), it.flatten().toSExpr())) }

private fun FlatApp.toSExpr(): SExpr =
    if (this.args.isEmpty()) SExpr.Atm(name)
    else SExpr.Lst(listOf(SExpr.Atm(name)) + args.map { it.toSExpr() })

fun parseExamples(sexps: Collection<String>): Query =
    examplesFromSexps(sexps.map { parseSExpr(it) })

fun parseTest(name: String): QuerySpec {
    val exs = readExamples(name)
    return QuerySpec(
        name, parseExamples(exs.second.filter { it.isNotBlank() }), oracleFromAssignment(exs.first))
}

fun oracleFromAssignment(context: String) = CheckingOracle(assignment(context))

private fun assignment(context: String) =
    context.split('\t').associate {
        val assign = parseSExpr(it)
        require(assign is SExpr.Lst && assign.elements.size == 2 && assign.elements[0] is SExpr.Atm)
        (assign.elements[0] as SExpr.Atm).value to assign.elements[1].toType()
    }

private fun examplesFromSexps(sexps: Collection<SExpr>): Query {
    val exsWithNames = sexps.map { it.toSignedExample() }
    val exs = exsWithNames.map { Pair(it.second, it.first) }
    val (pos, neg) = splitExamples(exs)
    return Query(pos, neg)
}

/** Posex, negex, names mentioned */
private fun splitExamples(exs: List<Pair<Example, Boolean>>): Pair<List<Example>, List<Example>> {
    val (pos, neg) = exs.partition { (_, sign) -> sign }
    return Pair(
        pos.map { (ex, _) -> ex },
        neg.map { (ex, _) -> ex },
    )
}

private fun SExpr.toSignedExample(): Triple<Boolean, Example, Set<String>> =
    when (this) {
        is SExpr.Atm -> {
            throw Exception("Not an example")
        }
        is SExpr.Lst -> {
            require(this.elements.size == 2)
            require(this.elements[0] is SExpr.Atm)
            val sign = (this.elements[0] as SExpr.Atm).value
            require(sign == "+" || sign == "-")
            val (ex, names) = this.elements[1].toExpression()
            Triple(sign == "+", ex, names)
        }
    }

fun SExpr.toExpression(): Pair<Example, Set<String>> =
    when (this) {
        is SExpr.Atm -> {
            Pair(Name(this.value), setOf(this.value))
        }
        is SExpr.Lst -> {
            require(this.elements.isNotEmpty())
            val (apps, names) = this.elements.map { it.toExpression() }.unzip()
            fun leftAssocApp(apps: List<Example>): Example =
                if (apps.size == 1) apps[0] else App(leftAssocApp(apps.dropLast(1)), apps.last())
            Pair(leftAssocApp(apps), names.fold(setOf()) { a, n -> a.union(n) })
        }
    }

fun SExpr.toExample(): Example =
    when (this) {
        is SExpr.Atm -> Name(this.value)
        is SExpr.Lst -> {
            require(this.elements.isNotEmpty())
            val apps = this.elements.map { it.toExample() }
            fun leftAssocApp(apps: List<Example>): Example =
                if (apps.size == 1) apps[0] else App(leftAssocApp(apps.dropLast(1)), apps.last())
            leftAssocApp(apps)
        }
    }

fun String.toExample() = parseSExpr(this).toExample()

fun parseExample(s: String) = parseSExpr(s).toExpression().first

fun parseApp(s: String) = parseSExpr(s).toSignedExample().second

fun parseFlatExamples(sexps: Collection<String>): FlatQuery =
    flatExamplesFromSexps(sexps.map { parseSExpr(it) })

private fun flatExamplesFromSexps(sexps: Collection<SExpr>): FlatQuery {
    val exsWithNames = sexps.map { it.toFlatExample() }
    val exs = exsWithNames.map { Pair(it.second, it.first) }
    val names = exsWithNames.map { it.third }.fold(setOf<String>()) { a, b -> a.union(b) }
    val (pos, neg) = splitFlatExamples(exs)
    return FlatQuery(pos, neg, names.toList())
}

/** Posex, negex, names mentioned */
private fun splitFlatExamples(
    exs: List<Pair<FlatApp, Boolean>>
): Pair<List<FlatApp>, List<FlatApp>> {
    val (pos, neg) = exs.partition { (_, sign) -> sign }
    return Pair(
        pos.map { (ex, _) -> ex },
        neg.map { (ex, _) -> ex },
    )
}

private fun SExpr.toFlatExample(): Triple<Boolean, FlatApp, Set<String>> =
    when (this) {
        is SExpr.Atm -> {
            throw Exception("Not an example")
        }
        is SExpr.Lst -> {
            require(this.elements.size == 2)
            require(this.elements[0] is SExpr.Atm)
            val sign = (this.elements[0] as SExpr.Atm).value
            require(sign == "+" || sign == "-")
            val (ex, names) = this.elements[1].toFlatApplication()
            Triple(sign == "+", ex, names)
        }
    }

private fun SExpr.toFlatApplication(): Pair<FlatApp, Set<String>> =
    when (this) {
        is SExpr.Atm -> {
            Pair(FlatApp(this.value), setOf(this.value))
        }
        is SExpr.Lst -> {
            require(this.elements.isNotEmpty())
            val (apps, names) = this.elements.map { it.toFlatApplication() }.unzip()
            if (elements[0] is SExpr.Atm)
                Pair(
                    FlatApp((elements[0] as SExpr.Atm).value, apps.drop(1)),
                    names.fold(setOf()) { a, n -> a.union(n) })
            else
                TODO(
                    "Not yet implemented: Parsing application where the function is the result of an application"
                ) // Pair(Application(apps[0]))
        }
    }

fun parseFlatApp(s: String) = parseSExpr(s).toFlatApplication().first
