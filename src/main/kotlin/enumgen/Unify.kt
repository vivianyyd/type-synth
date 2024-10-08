package enumgen

typealias Context = MutableMap<Variable, Type>

// TODO throughout this file need to make consistent which context gets returned with Errors
class Unify {
    /** Assumes [target] is not a variable with an entry in [map]. */
    private fun unifyVar(v: Variable, target: Type, map: Context): Pair<Type, Context> =
        map[v]?.let { unify(it, target, map) } ?: run {
            map[v] = target
            Pair(target, map)
        }

    private fun unify(a: Type, b: Type, map: Context): Pair<Type, Context> = when (a) {
        is Variable -> {
            when (b) {
                is Variable -> { // Unwrap b if possible
                    map[b]?.let { unify(a, it, map) } ?: unifyVar(a, b, map)
                }
                is Function, is Node -> unifyVar(a, b, map)
                is Error -> Pair(b, map)
                is TypeHole -> Pair(a, map)
            }
        }
        is Function -> {
            when (b) {
                is Variable -> unifyVar(b, a, map)
                is Function -> {
                    val (param, innerContext) = unify(a.param, b.param, map)
                    if (param is Error) Pair(param, innerContext)
                    val (outputType, outerContext) = unify(a.out, b.out, innerContext)
                    if (outputType is Error) Pair(outputType, outerContext)
                    Pair(
                        Function(param, outputType),
                        outerContext  // If unifying inputs of (a->a)->a and (int->int)->int, need to store a:=int
                    )
                }  // TODO think about variable shadowing. I think a->(a->a) is fine! what about unifying a-> (a->b) if they have diff names. should each type just have disjoint sets of variables?
                is Node -> Pair(Error(b, a, ErrorCategory.NODE_FUNCTION), map)
                is Error -> Pair(b, map)
                is TypeHole -> Pair(a, map)
            }
        }
        is Node -> when (b) {
            is Variable -> unifyVar(b, a, map)
            is Node -> {
                if (a.label != b.label) Pair(Error(a, b, ErrorCategory.LABEL_MISMATCH), map)
                if (a.typeParams.size != b.typeParams.size) Pair(
                    Error(a, b, ErrorCategory.PARAM_QUANTITY_MISMATCH),
                    map
                )
                var currMap = map
                var error: Pair<Type, Context>? = null
                val params = a.typeParams.indices.map {
                    val (param, newMap) = unify(a.typeParams[it], b.typeParams[it], currMap)
                    if (param is Error) error = Pair(param, currMap)
                    currMap = newMap
                    param
                }
                error ?: Pair(Node(a.label, params), currMap)
            }
            is Function -> Pair(Error(a, b, ErrorCategory.NODE_FUNCTION), map)
            is Error -> Pair(b, map)
            is TypeHole -> Pair(a, map)
        }
        is Error -> Pair(a, map)
        is TypeHole -> Pair(b, map)
    }

    fun apply(f: Type, arg: Type, map: Context): Pair<Type, Context> {
        if (f !is Function) return Pair(Error(f, arg, ErrorCategory.APPLIED_NON_FUNCTION), map)
        val (specializedF, fnContext) = unify(f.param, arg, map)
        if (specializedF is Error) return Pair(specializedF, fnContext)
        return resolve((specializedF as Function).out, fnContext)
    }

    // Notice it's similar to unify
    /** Should never produce new errors */
    private fun resolve(t: Type, map: Context): Pair<Type, Context> = when (t) {
        is Error -> Pair(t, map)
        is TypeHole -> Pair(t, map)
        is Variable -> map[t]?.let { resolve(it, map) } ?: Pair(t, map)
        // I think we want to keep variables not in the Context, instead of throwing an error
        is Function -> {
            val (inT, inMap) = resolve(t.param, map)
            val (outT, outMap) = resolve(t.out, inMap)
            Pair(Function(inT, outT), outMap)
        }
        is Node -> {
            var currMap = map
            val params = (0 until t.typeParams.size).map {
                val (param, newMap) = resolve(t.typeParams[it], currMap)
                currMap = newMap
                param
            }
            assert(params.indexOfFirst { it is Error } == -1)  // TODO I think this is right..
            Pair(Node(t.label, params), currMap)
        }
    }
}
