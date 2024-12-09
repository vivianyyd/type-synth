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

class ExampleAnalysis(
    private val posExamples: Set<Application>,
    private val negExamples: Set<Application>
) {
    private fun partialArgParamCompatible(fn: String, fnTy: Type, arg: String, argTy: Type, tree: SearchTree): Boolean {
        val assignment =
            tree.root.names.associateWith { if (it == fn) fnTy else if (it == arg) argTy else SiblingHole(-1) }
        return posExamples.map { checkApplication(it, assignment) }.all { it !is Error }
    }

    fun partialArgsParamsCompatible(fn: String, t: Type, tree: SearchTree): Boolean {
        val exs = posExamples.filter { it.name == fn }
        val arguments = exs.flatMap { it.arguments ?: listOf() }.map { it.name }.toSet()
        val argTyRoots =
            arguments.associateWith { tree.getRootFor(it) }  // Should be no NPE, just single ChildHole
        return argTyRoots.all { (argName, treeRoot) ->
            val leaves = mutableListOf<TypeSearchNode>()
            val frontier = (treeRoot.children[0] ?: listOf()).toMutableList()
            while (frontier.isNotEmpty()) {
                val node = frontier.removeFirst()
                if (node.children.isEmpty() || node.children.all { it == null || it.isEmpty() }) leaves.add(node)
                else frontier.addAll(node.children.flatMap { it ?: listOf() })
            }
            leaves.any { leaf ->
                partialArgParamCompatible(fn, t, argName, leaf.type, tree)
            }
        }
    }

    // TODO actually flatten the posexs, negexs so each application is named, then enum types for everything in posexs names
    fun canBeEqual(expressions: Set<Application>): Boolean {
        return expressions.all { e ->
            posExamples.all { app ->
                expressions.all { ePrime -> works(replace(app, e, ePrime)) }
            }
        }
    }

    private fun replace(a: Application, e: Application, ePrime: Application): Application =
        if (a == e) ePrime else Application(a.name, a.arguments?.map { replace(it, e, ePrime) })

    private fun works(a: Application): Boolean = a in posExamples  // TODO replace with call to black box type checker

    // TODO once things work, figure out right way of organizing code. This is duplicate and rly bad
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
                val (resultType, resultContext) = Unify.apply(fn, argType, currContext)
                currContext = resultContext
                fn = resultType
            }
            return Pair(fn, currContext)
        }
        return checkAppRec(app, map, mutableMapOf()).first
    }
}
