package core.unification

import core.languages.Elab

/** Good style would be to hide this constructor somehow so it can only be instantiated by ElabV */
data class ElabConstrV(val v: Int, val instId: Int) : Substitutable<Elab>() {
    override fun toString() = "V${v}-$instId"
}

object ElabConstrL : CTypeConstructor<Elab>(mutableListOf()) {
    override fun match(other: CTypeConstructor<Elab>): Boolean = other is ElabConstrL

    override fun toString() = "L"
}
