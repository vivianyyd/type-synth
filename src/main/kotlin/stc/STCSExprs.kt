package stc

import util.SExpr
import util.SExprParser

fun Map<String, SymTypeC>.toSExpr() = SExpr.Lst(this.entries.map {
    SExpr.Lst(listOf(SExpr.Atm(it.key), it.value.toSExpr()))
})

fun outline(context: String): Projection {
    val s = SExprParser(context).parse()
    assert(s is SExpr.Lst)
    return Projection((s as SExpr.Lst).elements.associate {
        assert(it is SExpr.Lst && it.elements.size == 2 && it.elements[0] is SExpr.Atm)
        ((it as SExpr.Lst).elements[0] as SExpr.Atm).value to it.elements[1].toSTC()
    })
}

fun SExpr.toSTC(): SymTypeC = when (this) {
    is SExpr.Atm -> {
        assert(this.value != "->")
        val ids = value.substring(2).split('_').map { it.toInt() }
        when (value.substring(0, 2)) {
            "VL" -> VL(vId = ids[1], tId = ids[0])
            "VR" -> VR(vId = ids[1], tId = ids[0])
            "VB" -> VB(vId = ids[1], tId = ids[0])
            else -> throw Exception("Invalid variable parsed")
        }
    }
    is SExpr.Lst -> {
        assert(this.elements.isNotEmpty())
        assert(this.elements[0] is SExpr.Atm)
        val fst = this.elements[0] as SExpr.Atm
        if (fst.value == "->") {
            assert(this.elements.size == 3)
            F(left = this.elements[1].toSTC(), rite = this.elements[2].toSTC())
        } else {
            L(label = fst.value.toInt())
        }
    }
}

fun parseSymTypeC(s: String) = SExprParser(s).parse().toSTC()

fun SymTypeC.toSExpr(): SExpr = when (this) {
    is F -> SExpr.Lst(
        listOf(
            SExpr.Atm("->"),
            left.toSExpr(),
            rite.toSExpr()
        )
    )
    is L -> SExpr.Lst(listOf(SExpr.Atm("$label")))
    is VL -> SExpr.Atm("VL$this")
    is VR -> SExpr.Atm("VR$this")
    is VB -> SExpr.Atm("VB$this")
}

/*
Function (-> left rite)
Variable VLa VRa VBa
Label (label)
 */
