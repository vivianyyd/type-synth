package util.io

import oneast.*
import util.CheckingGroundTruthOracle

fun oracleFromAssignment(context: String) =
    CheckingGroundTruthOracle(
        context.split(';').associate {
            val assign = parseSExpr(it)
            require(
                assign is SExpr.Lst && assign.elements.size == 2 && assign.elements[0] is SExpr.Atm
            )
            (assign.elements[0] as SExpr.Atm).value to assign.elements[1].toType()
        })

fun SExpr.toType(): Type =
    when (this) {
        is SExpr.Atm -> {
            assert(this.value != "->")
            Variable(this.value.hashCode())
        }
        is SExpr.Lst -> {
            assert(this.elements.isNotEmpty())
            assert(this.elements[0] is SExpr.Atm)
            val fst = this.elements[0] as SExpr.Atm
            if (fst.value == "->") {
                assert(this.elements.size == 3)
                Arrow(this.elements[1].toType(), this.elements[2].toType())
            } else {
                NamedLabel(
                    label = fst.value.hashCode(),
                    params = this.elements.drop(1).map { it.toType() })
            }
        }
    }

fun parseType(s: String) = parseSExpr(s).toType()

fun Type.toSExpr(): SExpr =
    when (this) {
        is Arrow -> SExpr.Lst(listOf(SExpr.Atm("->"), l.toSExpr(), r.toSExpr()))
        is NamedLabel -> SExpr.Lst(listOf(SExpr.Atm("$label")) + params.map { it.toSExpr() })
        is Variable -> SExpr.Atm("$v")
        is Error,
        is THole -> throw Exception("Unsupported Type to SExpr")
    }

/*
Function (-> left rite)
Variable a
Label (l a b c), primitive (l)
 */
