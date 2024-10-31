package enumgen

/**
 * If [arguments] is null, the function [name] is not applied.
 *
 * Later: If [arguments] is empty, [name] is applied with no arguments. For now, unit doesn't exist, all fn must have an
 * argument to be applied, this is WLOG since we can just have a unit value be passed
 */
data class Application(val name: String, val arguments: List<Application>?)

typealias Assignment = MutableMap<String, Type>

class Enumerator(
    private val names: List<String>,
    private val posExamples: Set<Application>,
    private val MAX_TYPE_PARAMS: Int
) {
    // TODO("Assert that [posExamples] only contains names in [names]")
    private val u = Unify()  // TODO make this less dumb
    private val searchTree = SearchTree(names)

    private val labels = listOf("l0", "l1", "l2")

    private var varCounter = 0
    private fun freshVariable() =  // alph for readability
        Variable("${if (varCounter++ in 0..25) (varCounter + 96).toChar() else varCounter}")

    private fun typeExpansion(): List<Type> =
        (listOf(
            freshVariable(),
            Function(ChildHole(), ChildHole()),
        ) + (labels.flatMap { lbl ->
            (0..MAX_TYPE_PARAMS).map { numParams ->
                LabelNode(lbl, List(numParams) { ChildHole() })
            }
        })).toMutableList()

    /**
     * Returns list of possible children
     * [this] must contain a hole(?)
     */
    private fun Type.expansions(depth: Int): List<List<Type>> {
        assert(this.recursiveNumChildHoles() > 0)  // TODO maybe we can take this away at some pt
        when (this) {
            is ChildHole -> return listOf(typeExpansion())  // TODO I think this never needs to get called
            is Variable -> throw Exception("No expansions. alternative is to return empty list")
            is LabelNode -> {
                // If all holes, then fill in each param with multiple options and put sibling holes in all others
                if (this.directChildHoles()) {
                    assert(this.params.all { it is ChildHole })
                    return List(this.params.size) { filledPortInd ->
                        typeExpansion().map { exp ->
                            LabelNode(
                                this.label,
                                List(this.params.size) { i ->
                                    if (i == filledPortInd) exp else SiblingHole(depth)
                                }
                            )
                        }
                    }
                }
                // If not all holes (param is l of ??), no direct child holes. fill children recursively, propagate up
                else {
                    val holeChild = this.params.withIndex()
                        .filter { (_, ty) -> ty.recursiveNumChildHoles() != 0 }  // save intermediate result
                    // Only one child should have holes at a time
                    assert(holeChild.size == 1)
                    val exps = holeChild[0].value.expansions(depth + 1)
                    // call expansion on the child with holes, then return result of mapping across all expansions and
                    // attaching this node plus all the non-holey children (siblings of the direct child who had holes)
                    //this type but instead of hole in all params, fill this param w various things, put sibling holes in all the others
                    return exps.map {
                        it.map { exp ->
                            LabelNode(
                                this.label,
                                this.params.mapIndexed { i, p ->
                                    if (i == holeChild[0].index) exp else p
                                }
                            )
                        }
                    }
                }
            }
            is Error -> throw Exception("wth the heck error")
            is Function -> {
                if (this.directChildHoles()) {
                    assert(this.left is ChildHole && this.rite is ChildHole)
                    return listOf(
                        typeExpansion().map { exp ->
                            Function(left = exp, rite = SiblingHole(depth))
                        },
                        typeExpansion().map { exp ->
                            Function(left = SiblingHole(depth), rite = exp)
                        }
                    )
                } else {
                    val leftHasHole = this.left.recursiveNumChildHoles() != 0
                    assert(leftHasHole xor (this.rite.recursiveNumChildHoles() != 0))
                    val exps = (if (leftHasHole) left else rite).expansions(depth + 1)
                    return exps.map {
                        it.map { exp ->
                            Function(
                                left = if (leftHasHole) exp else this.left,
                                rite = if (leftHasHole) this.rite else exp
                            )
                        }
                    }
                }
            }
            is SiblingHole -> throw Exception("wth the heck sibling")
        }
    }

    /**
     * Exhaustively attempt to increase the height of [tree] by 1.
     * Returns true if a change was made.
     */
    private fun fill(tree: SearchNode, depth: Int): Boolean {
        if (tree.children.any { it == null }) {
            when (tree) {
                is LangNode -> {
                    tree.addChildren(ArrayList(names.map {
                        typeExpansion().map { ty -> TypeSearchNode(ty) }.toMutableList()
                    }))
                }
                is TypeSearchNode -> {
                    if (tree.numPorts > 0) tree.addChildren(tree.type.expansions(depth).map { optionsForPort ->
                        optionsForPort.map { ty -> TypeSearchNode(ty) }.toMutableList()
                    })
                }
            }
            return true
        }
        return tree.children.fold(false) { acc, port ->
            acc || port!!.fold(false) { a, option ->
                a || fill(option, depth + 1)
            }
        }
    }

    private fun unfilledPorts(): Boolean {
        TODO()
    }

    fun enumerate(): Set<Assignment> {
        var x = 0
        while (unfilledPorts() && x < 5) { // TODO remove this safeguard
            // Each time filling, keep track of new leaves
            // test all children of new leaves from previous round (the children are the new leaves,
            //  but we access them thru their parents so we can delete them from the tree)
            //  and prune all the ones that will never work regardless of sibling hole values
            // now the new leaves set (once we also delete the failures from there too) is the leaf parent set for the next round

            x++
            if (x == 5) println("HIT THE SAFEGUARD")
        }
        return TODO()
    }

    private fun checkApplication(app: Application, map: Map<String, Type>): Type =
        checkApplicationHelper(app, map, mutableMapOf()).first

    private fun checkApplicationHelper(
        app: Application,
        map: Map<String, Type>,
        context: Context
    ): Pair<Type, Context> {
        var currContext = context
        var fn = map[app.name] ?: throw Exception("Function name not found")
        app.arguments?.forEach {
            val (argType, newContext) = checkApplicationHelper(it, map, currContext)
            currContext = newContext
            val (resultType, resultContext) = u.apply(fn, argType, currContext)
            currContext = resultContext
            fn = resultType
        }
        return Pair(fn, currContext)
    }
}