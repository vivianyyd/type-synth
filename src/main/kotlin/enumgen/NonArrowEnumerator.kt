package enumgen

import enumgen.types.*
import enumgen.types.Function
import enumgen.visualizations.SearchStateVisualizer
import util.FlatQuery

class NonArrowEnumerator(
    private val query: FlatQuery,
    skeletons: Map<String, Type>
) {
    private var vizFileID = 0

    private val state = SearchState(skeletons)
    private val exampleAnalysis = ExampleAnalysis(query)

    private fun freshVariable() = Variable("a")
    private fun holeExpansion(): List<Type> =
        (listOf(
            freshVariable(),
//            Function(ChildHole(), ChildHole()),
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
                    fun childHolesToSibs(t: Type, depth: Int): Type = when (t) {
                        is Error, is SiblingHole, is Variable -> t
                        is Function -> Function(childHolesToSibs(t.left, depth), childHolesToSibs(t.rite, depth))
                        is LabelNode -> LabelNode(t.label, t.params.map { childHolesToSibs(it, depth) })
                        is ChildHole -> SiblingHole(depth)
                    }

                    if (this.left is ChildHole && this.rite is ChildHole) {
                        return listOf(
                            holeExpansion().map { exp ->
                                Function(left = exp, rite = SiblingHole(depth))
                            },
                            holeExpansion().map { exp ->
                                Function(left = SiblingHole(depth), rite = exp)
                            }
                        )
                    } else if (this.left is ChildHole) {
                        return listOf(holeExpansion().map { exp ->
                            Function(left = exp, rite = childHolesToSibs(this.rite, depth))
                        }) + this.rite.expansions(depth).map { port ->
                            port.map { exp ->
                                Function(left = SiblingHole(depth), rite = exp)
                            }
                        }
                    } else if (this.rite is ChildHole) {
                        return this.left.expansions(depth).map { port ->
                            port.map { exp ->
                                Function(left = exp, rite = SiblingHole(depth))
                            }
                        } + listOf(
                            holeExpansion().map { exp ->
                                Function(left = childHolesToSibs(this.rite, depth), rite = exp)
                            })
                    } else throw Exception("Can't happen")
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
            query.names.associateWith {
                val tree = state.tree(it)
                // We might have initialized the search state to contain an arrow skeleton
                if (tree.ports.any { it.isNotEmpty() }) tree.ports.flatten() else listOf(tree)
            }.toMutableMap()

        var depth = -1
        // Deep enumeration/vertical growing step
        viz("init")
        while (unfilledPorts(leafParents)) {
            depth++
            val nodesTofill = leafParents.filter { (_, v) -> v.isNotEmpty() }
            val changed = nodesTofill.mapValues { (_, nodes) -> nodes.map { fill(it, depth) } }
            changed.forEach { (name, changes) ->
                val keep = changes.zip(nodesTofill[name]!!).filter { (change, _) -> change }.map { it.second }
                leafParents[name] = keep
            }
            viz("fill")
            // Prune leaf if type is wrong shape regardless of type-siblings


            // TODO There is a bug here which causes me to somehow only record when pruning doesn't occur on one of the branches or something.
            val parentsPruned = leafParents.keys.associateWith { fn ->
                val parents = leafParents[fn]!!
                parents.associateWith { parent ->
                    var pruned = false
                    parent.ports.forEach { options ->
                        val prunedSome = options.retainAll { ty ->
                            val passesPosExs = passesPositives(fn, ty.type)
                            // If never fully applied, it's definitely this node that introduced the issue.
                            // TODO this might actually be bad
                            val fullyApplied = applied(fn, ty.type)
                            val pruneDueToPrimitiveParam = prunePrimitiveParam(fn, ty.type)
                            passesPosExs && fullyApplied && !pruneDueToPrimitiveParam
                        }
                        options.retainAll { ty ->
                            !(nullary(fn) && hasVariables(ty.type))
                            // Check for nullary type params after pruning unapplied functions, so we know they're nullary.
                        }
                        val prunedMore = options.retainAll { ty ->
                            // After posex validation so we don't have to worry abt non-fn types w application examples
                            // After pruning nullary fns with type params, bc useless variables erroneously unify.
                            //    We probably wouldn't need to do this if we didn't only examine leaves when pruning
                            val argsParamsCompatible =
                                exampleAnalysis.partialArgsParamsCompatible(fn, ty.type, state)
                            argsParamsCompatible// && unifies(ty.type, skeletons[fn]!!)
                        }
                        pruned = pruned || prunedSome || prunedMore
                        // If all we pruned was a useless parameter for nullary, do not mark a change; stop enum.
                        // Variable doesn't have any children, so pruning it shouldn't affect the course of enum (?)
                    }
                    // NO Big prune!
//                    if (!pruned) parent.ports.forEach { children ->
//                        children.removeIf { it.type.apex() is Function }
//                        children.clear()
//                    }
                    pruned
                }
            }

            viz("pruned")

            if (!(parentsPruned.any { (_, nodePruned) -> nodePruned.any { (_, b) -> b } })) {
                println("No pruning occurred!")
                break
            }

            query.names.forEach { name ->
                // TODO this should be port specific? we pause/continue enum on port level
                val (nodesThatChanged, noChange) = leafParents[name]!!.partition { parentsPruned[name]!![it]!! }
                // Next round of leaves will be current leaves' children. We always move onto next layer, so we can
                // defer propagating up w/o accidental infinite loop of enuming and pruning the same node repeatedly
//                leafParents[name] = nodesThatChanged.flatMap { it.ports.flatten() }

                // Always grow regardless of prune
                leafParents[name] = leafParents[name]!!.flatMap { it.ports.flatten() }
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

//        val contexts = state.contextsWithVariables(2)


        val contexts = state.contexts()
        println("Contexts: ${contexts.size}")
        val passesPos = contexts.filter { assignmentPassesPositives(it) }
        println("Filter- passes all positives: ${passesPos.size}")

        val exploded =
            passesPos.flatMap { it.populateVariablesPartitionBlowup(state.names.associateWith { nullary(it) }, 2) }
        println("Exploded contexts: ${exploded.size}")

        println("Total negexs: ${query.negExamples.size}")
        val negs = exploded.map { query.negExamples.count { ex -> checkApplication(ex, it) is Error } }
        println("Max rejected by exploded desired stuff: ${negs.max()}")
//        println("Min: ${negs.min()}")
//
        val bestWithNegs = exploded.filterIndexed { i, _ -> negs[i] == negs.max() }
        println("Candidates which reject the max number of examples: ${bestWithNegs.size}")
        val cands = (bestWithNegs.joinToString(separator = "\n"))
        println(cands)
//        val file = File("example.txt")
//        file.writeText(cands)

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

//        val explodedDesired = desiredIndices.map { passesPos[it] }.flatMap { it.populateVariablesPartitionBlowup(2) }
//        println("Exploded desired contexts: ${explodedDesired.size}")
//
//        println("Total negexs: ${negExamples.size}")
//        val negs = explodedDesired.map { negExamples.count { ex -> checkApplication(ex, it) is Error } }
//        println("Max rejected by exploded desired stuff: ${negs.max()}")
//        println("Min: ${negs.min()}")
//
//        val bestWithNegs = explodedDesired.filterIndexed { i, _ -> negs[i] == negs.max() }
//        println("Candidates cherry picked which also reject the max number of examples: ${bestWithNegs.size}")
//        println(bestWithNegs.joinToString(separator = "\n"))

        return ""
    }

    private fun nullary(fn: String): Boolean {
        return state.tree(fn).ports[0].none { it.type is Function }
    }

    private fun hasVariables(t: Type): Boolean = when (t) {
        is Variable -> true
        is Error -> false
        is TypeHole -> false
        is Function -> hasVariables(t.left) || hasVariables(t.rite)
        is LabelNode -> t.params.any { hasVariables(it) }
    }

    private fun prunePrimitiveParam(fn: String, t: Type): Boolean {
        if (t !is Function) return false
        var height = 2
        // TODO wanna check for alllll parameters, so do the labelnode/height whatever check in a loop
        // Iterate to bottom-rightmost arrow node
        var curr: Function = t
        var next = curr.rite
        var prune = false
        // TODO clean up hella
        if (curr.left is LabelNode && (curr.left as LabelNode).params.isEmpty()) {
            // Check whether all examples have args in corresponding spot which can be the same type
            val argumentsUsed =
                query.posExamples.filter { it.name == fn }.mapNotNull { it.args.getOrNull(height - 2) }.toSet()
            prune = prune || !(exampleAnalysis.canBeEqual(argumentsUsed))
        }
        while (next is Function) {
            curr = next
            next = curr.rite
            height++
            if (curr.left is LabelNode && (curr.left as LabelNode).params.isEmpty()) {
                // Check whether all examples have args in corresponding spot which can be the same type
                val argumentsUsed =
                    query.posExamples.filter { it.name == fn }.mapNotNull { it.args.getOrNull(height - 2) }.toSet()
                prune = prune || !(exampleAnalysis.canBeEqual(argumentsUsed))
            }
        }
        return prune
    }

    private fun assignmentPassesPositives(assignment: Assignment): Boolean =
        query.posExamples.all { checkApplication(it, assignment) !is Error }

    private fun passesPositives(fn: String, t: Type): Boolean {
        val assignment = query.names.associateWith { if (it == fn) t else SiblingHole(-1) }
        return assignmentPassesPositives(assignment)
    }

    /** Checks whether the function is ever fully applied with the given hypothesis. */
    private fun applied(fn: String, t: Type): Boolean {
        val assignment = query.names.associateWith { if (it == fn) t else SiblingHole(-1) }
        // TODO memoize, this is obviously duplicated with [passesChecks]
        return !query.posExamples.filter { it.name == fn }.map { checkApplication(it, assignment) }
            .all { it is Function }
    }

    private fun viz(stage: String = "") =
        SearchStateVisualizer.viz(state, "${vizFileID++}${if (stage == "") "" else "-"}$stage")
}
