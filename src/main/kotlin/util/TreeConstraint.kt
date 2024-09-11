package util

interface TreeConstraint

data class Equality(val left: Thingy, val right: Thingy) : TreeConstraint {
    override fun toString() = "$left = $right"
}

interface Thingy

interface Label : Thingy

data class LiteralLabel(val label: String) : Label {
    override fun toString() = label
}

data class NodeLabel(val node: Tree) : Label {
    override fun toString() = "lbl($node)"
// TODO need a function that actually goes into the node and gets a label
}

interface Tree : Thingy

data class LiteralTree(val label: Label, val children: List<Tree>) : Tree {
    override fun toString() = "{$label<$children>}"
}

data class Parameter(val fn: Function, val index: Int): Tree

data class Child(val parent: Tree, val index: Int): Tree

data class Function(val string: String = TODO())
