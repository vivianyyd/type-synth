package enumgen

typealias Context = MutableMap<Variable, Type>

// TODO throughout this file need to make consistent which context gets returned with Errors
class Unify {
    /** Assumes [target] is not a variable with an entry in [map]. */
    private fun unifyVar(v: Variable, target: Type, map: Context): Pair<Type, Context> =
        map[v]?.let { unify(it, target, map) } ?: run {
            if (target is Variable) {
                val cmp = v.id.compareTo(target.id)
                if (cmp < 0) {
                    map[v] = target
                    Pair(target, map)
                }
                else if (cmp == 0) Pair(target, map) // TODO idk if this is right
                else {
                    map[target] = v
                    Pair(v, map)
                }
            } else {
                if (containsVar(v, target, map)) Pair(Error(v, target, ErrorCategory.VAR_REFERENCES_SELF), map)
                else {
                    map[v] = target
                    Pair(target, map)
                }
            }
        }

    private fun containsVar(v: Variable, t: Type, map: Context): Boolean {
        return when (t) {
            is Error -> false
            is Function -> containsVar(v, t.left, map) || containsVar(v, t.rite, map)
            is LabelNode -> t.params.fold(false) { a, ty -> a || containsVar(v, ty, map) }
            is TypeHole -> false
            is Variable -> if (t == v) true else {
                val ty = map[t]
                if (ty == null) false else containsVar(v, ty, map)
            }
        }
    }

    private fun unify(a: Type, b: Type, map: Context): Pair<Type, Context> = when (a) {
        is Variable -> {
            when (b) {
                is Variable -> { // Unwrap b if possible
                    map[b]?.let { unify(a, it, map) } ?: unifyVar(a, b, map)
                }
                is Function, is LabelNode -> unifyVar(a, b, map)
                is Error -> Pair(b, map)
                is TypeHole -> Pair(a, map)
            }
        }
        is Function -> {
            when (b) {
                is Variable -> unifyVar(b, a, map)
                is Function -> {
                    val (param, innerContext) = unify(a.left, b.left, map)
                    if (param is Error) Pair(param, innerContext)
                    val (outputType, outerContext) = unify(a.rite, b.rite, innerContext)
                    if (outputType is Error) Pair(outputType, outerContext)
                    Pair(
                        Function(param, outputType),
                        outerContext  // If unifying inputs of (a->a)->a and (int->int)->int, need to store a:=int
                    )
                }  // TODO think about variable shadowing. I think a->(a->a) is fine! what about unifying a-> (a->b) if they have diff names. should each type just have disjoint sets of variables?
                is LabelNode -> Pair(Error(b, a, ErrorCategory.NODE_FUNCTION), map)
                is Error -> Pair(b, map)
                is TypeHole -> Pair(a, map)
            }
        }
        is LabelNode -> when (b) {
            is Variable -> unifyVar(b, a, map)
            is LabelNode -> {
                if (a.label != b.label) Pair(Error(a, b, ErrorCategory.LABEL_MISMATCH), map)
                if (a.params.size != b.params.size) Pair(
                    Error(a, b, ErrorCategory.PARAM_QUANTITY_MISMATCH),
                    map
                )
                var currMap = map
                var error: Pair<Type, Context>? = null
                val params = a.params.indices.map {
                    val (param, newMap) = unify(a.params[it], b.params[it], currMap)
                    if (param is Error) error = Pair(param, currMap)
                    currMap = newMap
                    param
                }
                error ?: Pair(LabelNode(a.label, params), currMap)
            }
            is Function -> Pair(Error(a, b, ErrorCategory.NODE_FUNCTION), map)
            is Error -> Pair(b, map)
            is TypeHole -> Pair(a, map)
        }
        is Error -> Pair(a, map)
        is TypeHole -> Pair(b, map)
    }

    fun apply(f: Type, arg: Type, map: Context): Pair<Type, Context> {
        // TODO figure out what to output if f is a hole. alternatively just always enum functions first but sometimes cyclic
        if (f is TypeHole) return Pair(f, map) // TODO this is not quite right
        if (f !is Function) return Pair(Error(f, arg, ErrorCategory.APPLIED_NON_FUNCTION), map)
        val (parameter, fnContext) = unify(f.left, arg, map)
        if (parameter is Error) return Pair(parameter, fnContext)
        return resolve(f.rite, fnContext)
    }

    // Notice it's similar to unify
    /** Should never produce new errors */
    private fun resolve(t: Type, map: Context): Pair<Type, Context> {
        return when (t) {
            is Error -> Pair(t, map)
            is TypeHole -> Pair(t, map)
            is Variable -> map[t]?.let { resolve(it, map) } ?: Pair(t, map)
            // I think we want to keep variables not in the Context, instead of throwing an error
            is Function -> {
                val (inT, inMap) = resolve(t.left, map)
                val (outT, outMap) = resolve(t.rite, inMap)
                Pair(Function(inT, outT), outMap)
            }
            is LabelNode -> {
                var currMap = map
                val params = (0 until t.params.size).map {
                    val (param, newMap) = resolve(t.params[it], currMap)
                    currMap = newMap
                    param
                }
                assert(params.indexOfFirst { it is Error } == -1)  // TODO I think this is right..
                Pair(LabelNode(t.label, params), currMap)
            }
        }
    }
}
