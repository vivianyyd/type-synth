package enumgen

typealias Assignment = Map<String, Type>

class Enumerator(
    private val names: List<String>,
    private val posExamples: Set<Application>,
    private val negExamples: Set<Application>,
//    private val MAX_TYPE_PARAMS: Int
) {
//    val DEPTH_BOUND = 4  // TODO remove this safeguard
    private var vizFileID = 0

    // TODO("Assert that [posExamples] and [negExamples] only contain names in [names]")
    private val state = SearchState(names)
    private val exampleAnalysis = ExampleAnalysis(posExamples, negExamples)

    //    private var varCounter = 0
    private fun freshVariable() = Variable("a")//Variable(varCounter++) // We decided we should start coarse
    private fun holeExpansion(): List<Type> =
        (listOf(
            freshVariable(),
            Function(ChildHole(), ChildHole()),
        ) + listOf(
//            LabelNode("d", List(2) { ChildHole() }),
            LabelNode("ℓ0", List(1) { ChildHole() }),
            LabelNode("ℓ1", List(0) { ChildHole() }),
            LabelNode("ℓ2", List(0) { ChildHole() }),
        )).toMutableList()

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
    private fun fill(tree: SearchNode, depth: Int): Boolean {
        if (tree.ports.any { it.isEmpty() }) {
            if (tree.numPorts > 0) {
                tree.type.expansions(depth).forEachIndexed { i, port ->
                    tree.ports[i] = port.map { ty -> SearchNode(ty) }.toMutableList()
                }
                return true
            }
            return false  // TODO think about this
        }
        // Do not change the order of the || with accumulators... Forces avoiding short circuit
        return tree.ports.fold(false) { acc, port ->
            port.fold(false) { a, option ->
                fill(option, depth + 1) || a
            } || acc
        }
    }

    /** it's easier to take the frontier than the search tree, bc no need to recurse to the leaves */
    private fun unfilledPorts(frontier: Map<String, List<SearchNode>>): Boolean =
        frontier.values.flatten().any { it.type.recursiveNumChildHoles() != 0 }

    fun enumerate(): String /* TODO Set<Assignment>*/ {
        /** Whether the most recent step affected the search space for a given function */
        var changedFns = names.map { true }

        val leafParents: MutableMap<String, List<SearchNode>> =
            names.associateWith { listOf(state.tree(it)) }.toMutableMap()

        // Deep enumeration/vertical growing step
//        var iter = 0
        viz("init")
        while (unfilledPorts(leafParents)) {  // && iter < DEPTH_BOUND
            // Expand only types that changed in the past
            changedFns = state.allTrees.zip(changedFns).map { (root, changed) ->
                if (changed) fill(root, 0) else false
            }
            viz("fill")

            // Prune leaf if type is wrong shape regardless of type-siblings
            val pruned = state.names.associateWith { false }.toMutableMap()
            leafParents.forEach { (fn, parents) ->
                parents.map { parent ->
                    parent.ports.forEach { options ->
                        val prunedSome = options.retainAll { ty ->
                            val passesPosExs = passesPositives(fn, ty.type)
                            // If never fully applied, it's definitely this node that introduced the issue.
                            // We can do something different if we have glass box access to *why* type checking failed
                            val fullyApplied = applied(fn, ty.type)
                            val pruneDueToPrimitiveParam = prunePrimitiveParam(fn, ty.type)
                            passesPosExs && fullyApplied && !pruneDueToPrimitiveParam
                        }
                        options.retainAll { ty ->
                            !nullaryHasTypeParams(fn, ty.type)
                            // Check for nullary type params after pruning unapplied functions, so we know they're nullary. TODO this is jank
                        }
                        val prunedMore = options.retainAll { ty ->
                            // After posex validation so we don't have to worry abt non-fn types w application examples
                            // After pruning nullary fns with type params, bc useless variables erroneously unify.
                            //    We probably wouldn't need to do this if we didn't only examine leaves when pruning
                            val argsParamsCompatible =
                                exampleAnalysis.partialArgsParamsCompatible(fn, ty.type, state)
                            argsParamsCompatible
                        }
                        pruned[fn] = pruned[fn]!! || prunedSome || prunedMore
                        // If all we pruned was a useless parameter for nullary, do not mark a change; stop enum.
                        // I think the nice explanation for this is that variable doesn't have any children? TODO think
                    }
                }
            }
            // Set changed to false for fn if pruning did nothing, even if filling did something
            changedFns = state.names.zip(changedFns).map { (fn, changed) ->
                if (!pruned[fn]!!) false else changed
            }

            // Next round of leaves will be current leaves' children
            /* We don't need to worry about the following infinite loop:
             enum l _, enum l 'a, prune l 'a *without immediately propagating pruning up*, enum l _ again.
             Since leafParents changes, we always move onto next layer. We can defer propagating up */
            names.forEachIndexed { i, n ->
                if (!changedFns[i]) {
                    leafParents[n]!!.forEach { parent ->
                        parent.ports.forEach { it.clear() }
                    }
                    /* TODO This removes newly enumerated nodes in a layer if we weren't able to prune any of them
                        This erroneously removes nodes that we want, such as l0(l1()) for []i.
                        But eliding it gives us out of memory error.
                        also this is brittle: Only works because if it didn't change from pruning,
                        we can get rid of the children. Fine with jank fix for now bc this will be improved when
                        we pause enumeration on branch level rather than fn level */
                    leafParents[n] = listOf()  // We won't be enumerating any further
                } else leafParents[n] = leafParents[n]!!.flatMap { it.ports.flatten() }
            }
            // TODO how to decide when done / move onto sibling step?

            viz("pruned")

            if (changedFns.all { !it }) {
                println("No pruning occurred!")
                break
            }
//            if (++iter == DEPTH_BOUND) println("HIT THE SAFEGUARD")
        }
        // Some leaves might be unfilled here if we realized we weren't getting any changes from pruning
        // Fn sibling resolution step

        return ""
    }

    private fun nullaryHasTypeParams(fn: String, t: Type): Boolean {
        val nullary = state.tree(fn).ports[0].none { it.type is Function }
        val hasParams = hasParams(t)
        return nullary && hasParams
    }

    private fun hasParams(t: Type): Boolean = when (t) {
        is Variable -> true
        is Error -> false
        is TypeHole -> false
        is Function -> hasParams(t.left) || hasParams(t.rite)
        is LabelNode -> t.params.any { hasParams(it) }
    }

    private fun prunePrimitiveParam(fn: String, t: Type): Boolean {
        if (t !is Function) return false
        var height = 2
        // Iterate to bottom-rightmost arrow node
        var curr: Function = t
        var next = curr.rite
        while (next is Function) {
            curr = next
            next = curr.rite
            height++
        }
        if (height != t.height) return false  // We didn't fill this fn recently, so no need to prune against examples
        // Check if left child is a primitive
        return if (curr.left is LabelNode && (curr.left as LabelNode).params.isEmpty()) {
            // Check whether all examples have args in corresponding spot which can be the same type
            val argumentsUsed = posExamples.filter { it.name == fn }.mapNotNull { it.arguments?.getOrNull(height - 2) }
            // TODO More general: Check that they can all simultaneously unify with the proposed type. Then the param
            //   in question need not be a primitive literal to do the check
            //   edit, idk what I meant by this. Think about it again
            !(exampleAnalysis.canBeEqual(argumentsUsed.toSet()))
        } else false  // Left child isn't primitive
    }

    private fun assignmentPassesPositives(assignment: Assignment): Boolean =
        posExamples.all { checkApplication(it, assignment) !is Error }

    private fun passesPositives(fn: String, t: Type): Boolean {
        val assignment = names.associateWith { if (it == fn) t else SiblingHole(-1) }
        return assignmentPassesPositives(assignment)
    }

    /** Checks whether the function is ever fully applied with the given hypothesis. */
    private fun applied(fn: String, t: Type): Boolean {
        val assignment = names.associateWith { if (it == fn) t else SiblingHole(-1) }
        // TODO memoize, this is obviously duplicated with [passesChecks]
        return !posExamples.filter { it.name == fn }.map { checkApplication(it, assignment) }.all { it is Function }
    }

    private fun viz(stage: String = "") = Visualizer.viz(state, "${vizFileID++}${if (stage == "") "" else "-"}$stage")
}
