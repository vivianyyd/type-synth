package symbolicgen

typealias PortContents = MutableList<SymbolicType>

sealed interface SymbolicType {
    var parent: Parent?
}

/** The symbolic type if we decide to use this node. Kills all port siblings along the path to this node */
fun SymbolicType.determinedTypeSoFar(): SymbolicType {
    if (this is Error) return this
    if (this.parent == null) return this
    val p = this.parent as Parent
    val newParent =
        if (p.index == 0) Function(mutableListOf(this), p.node.rite, p.node.parent)
        else Function(p.node.left, mutableListOf(this), p.node.parent)
    return newParent.determinedTypeSoFar()
}

/** When node [n] has parent [p], the [index]th child of [p] is [n]. */
data class Parent(val node: Function, val index: Int)

sealed class AbstractType(override var parent: Parent?) : SymbolicType

class Variable(override var parent: Parent? = null) : AbstractType(parent) {
    override fun toString(): String = "V"
}

class Function(
    val left: PortContents = mutableListOf(),
    val rite: PortContents = mutableListOf(),
    override var parent: Parent? = null
) :
    AbstractType(parent) {
    init {
        left.forEach { it.parent = Parent(this, 0) }
        rite.forEach { it.parent = Parent(this, 1) }
    }

    override fun toString(): String = "$left -> $rite"
}

class Label(override var parent: Parent? = null) : AbstractType(parent) {
    override fun toString(): String = "L"
}

class Hole(override var parent: Parent? = null) : AbstractType(parent) {
    override fun toString(): String = "_"
}

fun main() {
    val special = Label()
    val t = Function(
        mutableListOf(
            Variable(),
            Label()
        ),
        mutableListOf(
            Variable(),
            Function(
                mutableListOf(
                    Variable(),
                    Label()
                ),
                mutableListOf(
                    special,
                    Variable()
                )
            )
        )
    )
    println(t)
    println(special.determinedTypeSoFar())
}
