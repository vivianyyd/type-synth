package enumgen.types

import enumgen.*
import util.Application

fun checkApplication(app: Application, map: Assignment): Type {
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
