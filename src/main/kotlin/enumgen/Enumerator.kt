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
        assert(this.recursiveNumChildHoles() > 0)
        when (this) {
            is ChildHole -> return listOf(holeExpansion())  // I think this never needs to get called
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

    fun enumerate(): String {
        var iter = 1
        val leafParents: MutableMap<String, List<SearchNode>> =
            names.associateWith { listOf(state.tree(it)) }.toMutableMap()

        // Deep enumeration/vertical growing step
        viz("init")
        while (unfilledPorts(leafParents)) {
            println(iter)
            // Expand only types that changed in the past
            val fnsTofill = leafParents.filter { (_, v) -> v.isNotEmpty() }.keys
            val changed = fnsTofill.map { fill(state.tree(it), 0) }
            changed.zip(fnsTofill).filter { (c, _) -> !c }.forEach { (_, f) ->
                leafParents[f] = listOf()
            }
            viz("fill")
            // Prune leaf if type is wrong shape regardless of type-siblings


            // TODO There is a bug here which causes me to somehow only record when pruning doesn't occur on one of the branches or something.
            val parentsPruned = leafParents.keys.associateWith { fn ->
                val parents = leafParents[fn]!!
                parents.associateWith { parent ->
                    var p = false
                    parent.ports.forEach { options ->
                        val prunedSome = options.retainAll { ty ->
                            val passesPosExs = passesPositives(fn, ty.type)
                            // If never fully applied, it's definitely this node that introduced the issue.
                            val fullyApplied = applied(fn, ty.type)
                            val pruneDueToPrimitiveParam = prunePrimitiveParam(fn, ty.type)

                            if (!(passesPosExs && fullyApplied && !pruneDueToPrimitiveParam) && iter > 2) println("Pruned ${ty.type} for $fn")

                            passesPosExs && fullyApplied && !pruneDueToPrimitiveParam
                        }
                        options.retainAll { ty ->
                            !nullaryHasTypeParams(fn, ty.type)
                            // Check for nullary type params after pruning unapplied functions, so we know they're nullary.
                        }
                        val prunedMore = options.retainAll { ty ->
                            // After posex validation so we don't have to worry abt non-fn types w application examples
                            // After pruning nullary fns with type params, bc useless variables erroneously unify.
                            //    We probably wouldn't need to do this if we didn't only examine leaves when pruning
                            val argsParamsCompatible =
                                exampleAnalysis.partialArgsParamsCompatible(fn, ty.type, state)

                            if (!(argsParamsCompatible) && iter > 2) println("Pruned ${ty.type} for $fn")

                            argsParamsCompatible
                        }
                        p = p || prunedSome || prunedMore
                        // If all we pruned was a useless parameter for nullary, do not mark a change; stop enum.
                        // Variable doesn't have any children, so pruning it shouldn't affect the course of enum (?)
                    }
                    p
                }
            }

            viz("pruned")


            val tmp = parentsPruned.mapValues { (k, v) -> v.filter { (n, b) -> !b }.map { (n, b) -> n.type } }
            println(tmp)

            if (!(parentsPruned.any { (_, nodePruned) -> nodePruned.any { (_, b) -> b } })) {
                println("No pruning occurred!")


                // TODO maybe remove me, trying this out. On the very last iteration, if we didn't prune anything,
                //   we should do a big prune since we won't go back and enum here anyway
                names.forEach { name ->
                    val (nodesThatChanged, noChange) = leafParents[name]!!.partition { parentsPruned[name]!![it]!! }
                    println(noChange.size)
                    noChange.forEach { parent ->
                        parent.ports.forEach { p ->
                            p.clear()
                        }
                    }
                }

                break
            }

            names.forEach { name ->
                val (nodesThatChanged, noChange) = leafParents[name]!!.partition { parentsPruned[name]!![it]!! }
                // Next round of leaves will be current leaves' children. We always move onto next layer, so we can
                // defer propagating up w/o accidental infinite loop of enuming and pruning the same node repeatedly
                leafParents[name] = nodesThatChanged.flatMap { it.ports.flatten() }
            }
//            if (++iter == DEPTH_BOUND) println("HIT THE SAFEGUARD")
            iter++
        }

        viz("end")

        // TODO Start with blowup and no variable assignments, keep hole everywhere and everything one variable.
        //  We'll eliminate a lot of combinations. Then make variable assignments to those! Bc variable blowup is an
        //  operation on contexts and not types anyways.


//        fun t(s: String): Type = SExprParser(s).parse().toType()
//        val fav = mapOf(
//            "0" to "(l1)",
//            "tr" to "(l2)",
//            "[]i" to "(l0 (l1))",
//            "[]b" to "(l0 (l2))",
//            "[[]]i" to "(l0 (l0 (l1)))",
//            "cons" to "(-> a (-> (l0 a) (l0 a)))"
//        ).mapValues { (_, v) -> t(v) }
//        println(fav)
//        println("DOES THIS THING EVEN WORK ${assignmentPassesPositives(fav)}")

//        val contexts = state.contextsWithVariables(2)


//        val contexts = state.contexts()
//        println("Contexts: ${contexts.size}")
//        val passesPos = contexts.filter { assignmentPassesPositives(it) }
//        println("Filter- passes all positives: ${passesPos.size}")


//        val desiredIndices = passesPos.withIndex().filter { (_, it) ->
//            it["0"] is LabelNode && (it["0"] as LabelNode).params.isEmpty() && (it["0"] as LabelNode).label.contains("1") &&
//                    it["tr"] is LabelNode && (it["tr"] as LabelNode).params.isEmpty() && (it["tr"] as LabelNode).label.contains(
//                "2"
//            ) &&
//                    it["[]i"] is LabelNode && (it["[]i"] as LabelNode).params.isNotEmpty() &&
//                    it["[]b"] is LabelNode && (it["[]b"] as LabelNode).params.isNotEmpty() &&
//                    it["cons"] is Function && ((it["cons"] as Function).left is Variable) &&
//                    ((it["cons"] as Function).rite is Function) &&
//                    ((it["cons"] as Function).rite as Function).left !is Variable &&
//                    ((it["cons"] as Function).rite as Function).rite is LabelNode &&
//                    (((it["cons"] as Function).rite as Function).rite as LabelNode).label.contains("0") &&
//                    /*((it["cons"] as Function).left as Variable).id=="0" &&*/
//                    it["[[]]i"] is LabelNode && (it["[[]]i"] as LabelNode).params.isNotEmpty()
//        }.map { (i, _) -> i }

//        val exploded = desiredIndices.map{passesPos[it]}.flatMap { it.populateVariablesPartitionBlowup(2) }
//        println("Exploded examples: ${ exploded.size }")


//        println("Total negexs: ${negExamples.size}")
//        val negs = exploded.map { negExamples.count { ex -> checkApplication(ex, it) is Error } }
//        println("Max rejected by exploded desired stuff: ${negs.max()}")
//        println("Min: ${negs.min()}")
//
//
//        val bestWithNegs = exploded.filterIndexed { i, _ -> negs[i] == negs.max() }
//        println("Candidates which reject the max number of examples: ${bestWithNegs.size}")
//        println(bestWithNegs.joinToString(separator = "\n"))
//
//
//        println("WHAT WE WANTED THAT REJECTS MOST NEGS")
//        println(desiredIndices.filter { negs[it] == maxNegsByDesired  }.map{passesPos[it]}.joinToString(separator = "\n"))
        /*

         */

        return ""
    }

    /* The most freshly enumerated node in the type, it is of greatest depth other than sibling holes */
    fun Type.apex(): Type {
        if (this.directChildHoles()) return this
        when (this) {
            is Error, is TypeHole, is Variable -> return this
            is Function -> {
                if (this.left.height == this.rite.height) {
                    assert((this.left is SiblingHole).xor(this.rite is SiblingHole))
                    return if (this.left is SiblingHole) this.rite.apex() else this.left.apex()
                }
                return if (this.left.height > this.rite.height) this.left.apex() else this.rite.apex()
            }
            is LabelNode -> {
                if (this.params.isEmpty()) return this
                val heights = this.params.map { it.height }
                val longest = heights.filter { it == heights.max() }
                if (longest.size == 1) return this.params.filter { it.height == heights.max() }[0].apex()
                val nonSiblingHole = this.params.filter { it !is SiblingHole }
                assert(nonSiblingHole.size == 1)
                return nonSiblingHole[0].apex()
            }
        }
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
