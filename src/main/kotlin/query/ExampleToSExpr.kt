package query

import util.SExpr

fun sexpsFromExamples(exs: Collection<Example>, pos: Boolean): Collection<SExpr> = exs.map {
    SExpr.Lst(listOf(SExpr.Atm(if (pos) "+" else "-"), it.flatten().toSExpr()))
}

private fun FlatApp.toSExpr(): SExpr =
    if (this.args.isEmpty()) SExpr.Atm(name) else SExpr.Lst(listOf(SExpr.Atm(name)) + args.map { it.toSExpr() })
