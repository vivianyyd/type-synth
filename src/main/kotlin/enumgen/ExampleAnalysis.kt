package enumgen

import query.FlatApp
import query.FlatQuery
import types.Error
import types.SiblingHole
import types.Type
import types.checkApplication


class ExampleAnalysis(private val query: FlatQuery) {
    private val params: MutableMap<String, Int> = query.names.associateWith { 0 }.toMutableMap()
    private val posFor: MutableMap<String, MutableSet<FlatApp>> =
        query.names.associateWith { mutableSetOf<FlatApp>() }.toMutableMap()
    private val negFor: MutableMap<String, MutableSet<FlatApp>> =
        query.names.associateWith { mutableSetOf<FlatApp>() }.toMutableMap()

    init {
        fun helpPos(app: FlatApp) {
            params[app.name] = maxOf(params[app.name]!!, app.args.size)
            posFor[app.name]!!.add(app)
            app.args.forEach { helpPos(it) }
        }
        query.posExamples.forEach { helpPos(it) }

        fun helpNeg(app: FlatApp) {
            negFor[app.name]!!.add(app)
            app.args.forEach { helpNeg(it) }
        }
        query.negExamples.forEach { helpNeg(it) }

        query.names.forEach { params[it] = params[it]!! + 1 }  // Add output parameter
    }

    fun params(name: String): Int = params[name]!!
    fun posFor(name: String): Set<FlatApp> = posFor[name]!!
    fun negFor(name: String): Set<FlatApp> = negFor[name]!!

    private fun partialArgParamCompatible(
        fn: String,
        fnTy: Type,
        arg: String,
        argTy: Type,
        tree: SearchState
    ): Boolean {
        val assignment =
            tree.names.associateWith { if (it == fn) fnTy else if (it == arg) argTy else SiblingHole(-1) }
        return query.posExamples.map { checkApplication(it, assignment) }.all { it !is Error }
    }

    fun partialArgsParamsCompatible(fn: String, t: Type, tree: SearchState): Boolean {
        val exs = query.posExamples.filter { it.name == fn }
        val arguments = exs.flatMap { it.args }.map { it.name }.toSet()
        val argTyRoots =
            arguments.associateWith { tree.tree(it) }  // Should be no NPE, just single ChildHole
        return argTyRoots.all { (argName, treeRoot) ->
            val leaves = mutableListOf<SearchNode>()
            val frontier = (treeRoot.ports[0]).toMutableList()
            while (frontier.isNotEmpty()) {
                val node = frontier.removeFirst()
                if (node.ports.isEmpty() || node.ports.all { it.isEmpty() }) leaves.add(node)
                else frontier.addAll(node.ports.flatten())
            }
            leaves.any { leaf ->
                partialArgParamCompatible(fn, t, argName, leaf.type, tree)
            }
        }
    }

    // TODO actually flatten the posexs, negexs so each application is named, then enum types for everything in posexs names
    fun canBeEqual(expressions: Set<FlatApp>): Boolean {
        return expressions.all { e ->
            query.posExamples.all { app ->
                expressions.all { ePrime -> works(replace(app, e, ePrime)) }
            }
        }
    }

    private fun replace(a: FlatApp, e: FlatApp, ePrime: FlatApp): FlatApp =
        if (a == e) ePrime else FlatApp(a.name, a.args.map { replace(it, e, ePrime) })

    private fun works(a: FlatApp): Boolean = a in query.posExamples  // TODO replace with call to black box type checker
}
