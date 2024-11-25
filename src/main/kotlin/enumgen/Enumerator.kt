package enumgen

/**
 * If [arguments] is null, the function [name] is not applied.
 *
 * Later: If [arguments] is empty, [name] is applied with no arguments. For now, unit doesn't exist, all fn must have an
 * argument to be applied, this is WLOG since we can just have a unit value be passed
 * TODO idk wtf the above comment is saying, let's use ocaml model of no such thing as applying function with no
 *  arguments, need to apply with unit. Is this WLOG?
 */
data class Application(val name: String, val arguments: List<Application>?)

typealias Assignment = MutableMap<String, Type>

class Enumerator(
    private val names: List<String>,
    private val posExamples: Set<Application>,
    private val negExamples: Set<Application>,
    private val MAX_TYPE_PARAMS: Int
) {
    // TODO("Assert that [posExamples] and [negExamples] only contain names in [names]")
    private val u = Unify()  // TODO make this less dumb
    private val searchTree = SearchTree(names)

    private var varCounter = 0
    private fun freshVariable() = Variable(varCounter++)

    private fun holeExpansion(): List<Type> =
        (listOf(
            freshVariable(),
            Function(ChildHole(), ChildHole()),
        ) + listOf(
            LabelNode("ℓ0", List(1) { ChildHole() }),
            LabelNode("ℓ1", List(0) { ChildHole() }),
            LabelNode("ℓ2", List(0) { ChildHole() }),
        )).toMutableList()
//            (listOf("l0", "l1", "l2").flatMap { lbl ->
//                (0..MAX_TYPE_PARAMS).map { numParams ->
//                    LabelNode(lbl, List(numParams) { ChildHole() })
//                }})

    /**
     * Returns list of possible children
     * [this] must contain a hole(?)
     */
    private fun Type.expansions(depth: Int): List<List<Type>> {
        assert(this.recursiveNumChildHoles() > 0)  // TODO maybe we can take this away at some pt
        when (this) {
            is ChildHole -> return listOf(holeExpansion())  // TODO I think this never needs to get called
            is Variable -> throw Exception("No expansions. alternative is to return empty list")
            is LabelNode -> {
                // If all holes, then fill in each param with multiple options and put sibling holes in all others
                if (this.directChildHoles()) {
                    assert(this.params.all { it is ChildHole })
                    return List(this.params.size) { filledPortInd ->
                        holeExpansion().map { exp ->
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
                        holeExpansion().map { exp ->
                            Function(left = exp, rite = SiblingHole(depth))
                        },
                        holeExpansion().map { exp ->
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
    private fun fill(tree: TypeSearchNode, depth: Int): Boolean {
        if (tree.children.any { it == null }) {
            if (tree.numPorts() > 0) {
                tree.addChildren(tree.type.expansions(depth).map { optionsForPort ->
                    optionsForPort.map { ty -> TypeSearchNode(ty) }.toMutableList()
                })
                return true
            }
            return false  // TODO think about this
        }
        // Do not change the order of the || with accumulators... Forces avoiding short circuit
        return tree.children.fold(false) { acc, port ->
            port!!.fold(false) { a, option ->
                fill(option, depth + 1) || a
            } || acc
        }
    }

    /** it's easier to take the frontier than the search tree, bc no need to recurse to the leaves */
    private fun unfilledPorts(frontier: Map<String, List<SearchNode>>): Boolean =
        frontier.values.flatten().any {
            when (it) {
                is LangNode -> it.functions.any { f -> f == null }
                is TypeSearchNode -> it.type.recursiveNumChildHoles() != 0
            }
        }

    var visualization = ""
    val DEPTH_BOUND = 3  // TODO remove this safeguard

    fun enumerate(): String /* TODO Set<Assignment>*/ {
        // Init
        searchTree.root.addChildren(ArrayList(names.map { mutableListOf(TypeSearchNode(ChildHole())) }))

        /** Whether the most recent step affected the search space for a given function */
        var changedFns = searchTree.root.children.map { true }

        val leafParents: MutableMap<String, List<TypeSearchNode>> =
            names.withIndex().associate { (i, fn) -> fn to listOf(searchTree.root.functions[i]!![0]) }.toMutableMap()

        // Deep enumeration/vertical growing step
        var x = 0
        while (unfilledPorts(leafParents) && x < DEPTH_BOUND) {
            // Expand only types that changed in the past
            changedFns = searchTree.root.children.zip(changedFns).map { (portOptions, changed) ->
                if (changed) fill(portOptions!![0], 0)
                else false
            }

            // Prune leaf if type is wrong shape regardless of siblings
            val pruned = searchTree.root.names.associateWith { false }.toMutableMap()
            leafParents.forEach { (fn, parents) ->
                parents.map { parent ->
                    parent.children.forEach { options ->
                        println("About to prune expansions of ${parent.type} for function $fn")
                        println("Began with ${options?.size} options for current port")
                        val prunedSome = options?.retainAll { ty ->
                            val passesPosExs = passesChecks(fn, ty.type)
                            // TODO uncomment
//                            val fullyApplied = applied(fn, ty.type)  // if not fully applied, it's definitely this node that introduced the issue.
//                            if (!fullyApplied) println("pruned ${ty.type}")
                            passesPosExs //&& fullyApplied
                        } ?: false
                        pruned[fn] = pruned[fn]!! || prunedSome
                        println("Now have ${options?.size} options")
                    }
                }
            }
            // Set changed to false for fn if pruning did nothing, even if filling did something
            changedFns = searchTree.root.names.zip(changedFns).map { (fn, changed) ->
                if (!pruned[fn]!!) false else changed
            }

            if (changedFns.all { !it }) break
            // Next round of leaves will be current leaves' children
            /* We don't need to worry about the following infinite loop:
             enum l _, enum l 'a, prune l 'a *without immediately propagating pruning up*, enum l _ again.
             Since leafParents changes, we always move onto next layer. We can defer propagating up */
            names.forEachIndexed { i, n ->
                if (!changedFns[i]) leafParents[n] = listOf()  // We won't be enumerating any further
                else leafParents[n] = leafParents[n]!!.flatMap { it.children.filterNotNull().flatten() }
            }
            // TODO how to decide when done / move onto sibling step?

            /*

            TODO: Implement propagating pruning: If all children in one port die, the parent dies. Etc.
                only necessary to propagate before sibling merging steps, because vertical growth we have the changed
                flags to tell us what to grow and leafparents always moves on
             */
            visualization = Visualizer(searchTree).viz()

            if (++x == DEPTH_BOUND) println("HIT THE SAFEGUARD")
        }
//        println(Visualizer(searchTree).viz())
        // Some leaves might be unfilled here if we realized we weren't getting any changes from pruning
        // Fn sibling resolution step


        // TODO should we go back to the vertical step?

        return ""
    }

    private fun passesChecks(fn: String, t: Type): Boolean {
        val assignment = names.associateWith { if (it == fn) t else SiblingHole(-1) }
        // TODO pruning is very wrong right now! It's ok if something doesn't yet eliminate all negative examples!
        return posExamples.map { checkApplication(it, assignment) }.all { it !is Error }
        // && negExamples.map { checkApplication(it, assignment) }.all { it is Error }
    }

    /** Checks whether the function is ever fully applied with the given hypothesis. */
    /*
    TODO: There's a more general form of this which does the following.
     * Checks whether the function at greatest depth is ever applied.
     * The function in question is always unique since functions which are not ancestors are siblings/uncles/nephews
     * which are sibling holes.
     */
    private fun applied(fn: String, t: Type): Boolean {

        /*
        TODO let's just assume glass box access to type checker for now which allows us to skip this and assume
          we are given this info

        Examples

        singleton: 'a -> l['a]
        ex: singleton x
        candidate: (-1) -> (_ -> _) should be eliminated

        What about (_ -> _) -> -1

        fn list: l[_ -> _]
        Ok we'd have to first enum the type of get() so let's skip this for now
         */
        println("Checking if $fn is applied fully")
        val assignment = names.associateWith { if (it == fn) t else SiblingHole(-1) }
        // TODO memoize, this is obviously duplicated with [passesChecks]
        return !posExamples.map { checkApplication(it, assignment) }.all {
            println(it)
            /*

            TODO this currently doesn't work because of how functions with holes are unify/applied. Need to rethink

             */
            it is Function
        }
    }

    private fun checkApplication(app: Application, map: Map<String, Type>): Type {
        fun checkAppRec(
            app: Application,
            map: Map<String, Type>,
            context: Context
        ): Pair<Type, Context> {
            var currContext = context
            var fn = map[app.name] ?: throw Exception("Function name not found")
            app.arguments?.forEach {
                val (argType, newContext) = checkAppRec(it, map, currContext)
                currContext = newContext
                val (resultType, resultContext) = u.apply(fn, argType, currContext)
                currContext = resultContext
                fn = resultType
            }
            return Pair(fn, currContext)
        }
        return checkAppRec(app, map, mutableMapOf()).first
    }
}
