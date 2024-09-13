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

/** Completely concrete, no unknowns */
data class LiteralTree(val label: Label, val children: List<Tree>) : Tree {
    override fun toString() = "{$label<$children>}"
}

data class Parameter(/*val fn: String, */val index: Int): Tree

data class UnknownType(val name: String, val label: Label? = null, val children: List<Tree>? = null): Tree

data class Child(val parent: Tree, val index: Int): Tree

data class TypeApplication(val fn: String, val args: List<Tree>): Tree
// TODO enforce some invariant that args match params or idk. This might be unneeded until later let's first stick with queries that only involve one function
