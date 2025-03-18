package symbolicgen

import util.App
import util.Example
import util.Name

typealias Assignment = Map<String, SymbolicType>

/*
TODO What kind of information do we need to over/underapproximate when all variables/label arguments are unknown?
 */

fun check(ex: Example, solution: Assignment): SymbolicType {
    return when (ex) {
        is Name -> solution[ex.name] ?: throw Exception("Function ${ex.name} not found")
        is App -> {
            when (val fn = check(ex.fn, solution)) {
                is TypeHole -> fn
                is Function -> {
                    val argType = check(ex.arg, solution)
                    val inType = unify(fn.left, argType)
                    if (inType is Error) inType
                    else fn.rite
                }
                else -> Error(ErrorCategory.APPLIED_NON_FUNCTION, fn)
            }
        }
    }
}

fun unify(a: SymbolicType, b: SymbolicType): SymbolicType = when {
    a is Error -> a
    b is Error -> b
    a is TypeHole || a is Variable -> b
    b is TypeHole || b is Variable -> a
    a is Label && b is Label -> a
    a is Function && b is Function ->
        Function(unify(a.left, b.left), unify(a.rite, b.rite))
    (a is Label && b is Function) || (a is Function && b is Label) ->
        Error(ErrorCategory.LABEL_FUNCTION, a, b)
    else -> throw Exception("Impossible case")
}
