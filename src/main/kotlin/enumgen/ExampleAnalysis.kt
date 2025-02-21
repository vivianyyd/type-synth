package enumgen

import enumgen.types.*
import util.Application


class ExampleAnalysis(
    private val names: List<String>,
    private val posExamples: Set<Application>,
    private val negExamples: Set<Application>
) {
    private val params: MutableMap<String, Int> = names.associateWith { 0 }.toMutableMap()
    fun params(name: String): Int = params[name]!!
    private val posFor: MutableMap<String, MutableSet<Application>> = names.associateWith{mutableSetOf<Application>()}.toMutableMap()
    fun posFor(name: String): Set<Application> = posFor[name]!!
    private val negFor: MutableMap<String, MutableSet<Application>> = names.associateWith{mutableSetOf<Application>()}.toMutableMap()
    fun negFor(name: String): Set<Application> = negFor[name]!!

    init {
        fun helpPos(app: Application) {
            params[app.name] = maxOf(params[app.name]!!, app.arguments?.size ?: 0)
            posFor[app.name]!!.add(app)
            app.arguments?.forEach { helpPos(it) }
        }
        posExamples.forEach { helpPos(it) }

        fun helpNeg(app: Application) {
            negFor[app.name]!!.add(app)
            app.arguments?.forEach { helpNeg(it) }
        }
        negExamples.forEach { helpNeg(it) }

    }


    private fun partialArgParamCompatible(
        fn: String,
        fnTy: Type,
        arg: String,
        argTy: Type,
        tree: SearchState
    ): Boolean {
        val assignment =
            tree.names.associateWith { if (it == fn) fnTy else if (it == arg) argTy else SiblingHole(-1) }
        return posExamples.map { checkApplication(it, assignment) }.all { it !is Error }
    }

    fun partialArgsParamsCompatible(fn: String, t: Type, tree: SearchState): Boolean {
        val exs = posExamples.filter { it.name == fn }
        val arguments = exs.flatMap { it.arguments ?: listOf() }.map { it.name }.toSet()
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
}
