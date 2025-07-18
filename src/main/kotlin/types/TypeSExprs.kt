package types

import util.SExpr
import util.SExprParser

fun SExpr.toType(): Type = when (this) {
    is SExpr.Atm -> {
        assert(this.value != "->")
        Variable(this.value)
    }
    is SExpr.Lst -> {
        assert(this.elements.isNotEmpty())
        assert(this.elements[0] is SExpr.Atm)
        val fst = this.elements[0] as SExpr.Atm
        if (fst.value == "->") {
            assert(this.elements.size == 3)
            Function(left = this.elements[1].toType(), rite = this.elements[2].toType())
        } else {
            LabelNode(label = fst.value, params = this.elements.drop(1).map { it.toType() })
        }
    }
}

fun parseType(s: String) = SExprParser(s).parse().toType()

fun Type.toSExpr(): SExpr = when (this) {
    is Function -> SExpr.Lst(
        listOf(
            SExpr.Atm("->"),
            left.toSExpr(),
            rite.toSExpr()
        )
    )
    is LabelNode -> SExpr.Lst(listOf(SExpr.Atm(label)) + params.map { it.toSExpr() })
    is Variable -> SExpr.Atm(id)
    is Error, is TypeHole -> throw Exception("Unsupported Type to SExpr")
}

/*
Function (-> left rite)
Variable a
Label (l a b c), primitive (l)
 */
