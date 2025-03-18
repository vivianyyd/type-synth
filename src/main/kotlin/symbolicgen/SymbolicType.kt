package symbolicgen

sealed interface SymbolicType {
    var parent: Port?
}

/** The symbolic type if we decide to use this node. Kills all port siblings along the path to this node */
fun SymbolicType.determinedTypeSoFar(): SymbolicType {
    if (this is Error) return this
    if (this.parent == null) return this
    val p = this.parent as Port
    val newParent =
        if (p.index == 0) Function(listOf(this), p.node.rite, p.node.parent)
        else Function(p.node.left, listOf(this), p.node.parent)
    return newParent.determinedTypeSoFar()
}

data class Port(val node: Function, val index: Int)

sealed class AbstractType(override var parent: Port?) : SymbolicType

class Variable(override var parent: Port? = null) : AbstractType(parent) {
    override fun toString(): String = "V"
}

class Function(val left: List<SymbolicType>, val rite: List<SymbolicType>, override var parent: Port? = null) :
    AbstractType(parent) {
    init {
        left.forEach {it.parent = Port(this, 0)}
        rite.forEach {it.parent = Port(this, 1)}
    }
    override fun toString(): String = "$left -> $rite"  //"${if (left is Function) "($left)" else "$left"} -> $rite"
//    fun List<SymbolicType>.print() = if (this.size == 1) "$this[0]" else "$this"
//    return "${left.print()} -> ${rite.print()}"
}

class Label(override var parent: Port? = null) : AbstractType(parent) {
    override fun toString(): String = "L"
}

fun main() {
    val special = Label()
    val t = Function(
        listOf(
            Variable(),
            Label()
        ),
        listOf(
            Variable(),
            Function(
                listOf(
                    Variable(),
                    Label()
                ),
                listOf(
                    special,
                    Hole()
                )
            )
        )
    )
    println(t)
    println(special.determinedTypeSoFar())
}

/** A hole to be filled by a child node. */
class Hole(override var parent: Port? = null) : AbstractType(parent) {
    override fun toString(): String = "??"
}

// TODO This shouldn't be a type, just a result of SymbolicChecker. But Kotlin doesn't rly let us ad-hoc make SymbolicType a subclass of result
/** Unifies with everything, producing itself. Represents a type that can never successfully resolve. */
data class Error(val category: ErrorCategory, val t1: SymbolicType, val t2: SymbolicType? = null) : AbstractType(null)

enum class ErrorCategory {
    LABEL_FUNCTION,
    APPLIED_NON_FUNCTION
}
