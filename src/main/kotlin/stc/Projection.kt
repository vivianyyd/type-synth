package stc

import util.ParameterNode

class Projection(
    val outline: Map<String, SymTypeC>,
) {
    /** Number of parameters. Nullaries have one parameter. */
    val arities = outline.mapValues { (_, t) -> t.params() }

    val parameterToType = outline.entries.fold(mutableMapOf<ParameterNode, SymTypeC>()) { m, (name, tree) ->
        var curr = tree
        var count = 0
        while (curr is F) {
            m[ParameterNode(name, count)] = curr.left
            count++
            curr = curr.rite
        }
        m[ParameterNode(name, count)] = curr
        m
    }
}
