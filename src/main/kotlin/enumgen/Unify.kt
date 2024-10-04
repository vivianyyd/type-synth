package enumgen

typealias Context = MutableMap<Variable, Type>

fun err(map: Context) = Pair(Error, map)

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
                Error -> err(map)
                is TypeHole -> Pair(a, map)
            }
        }
        is Function -> {
            when (b) {
                is Variable -> unifyVar(b, a, map)
                is Function -> {
                    val (param, innerContext) = unify(a.param, b.param, map)
                    if (param is Error) err(innerContext)
                    val (outputType, outerContext) = unify(a.out, b.out, innerContext)
                    if (outputType is Error) err(outerContext)
                    Pair(
                        Function(param, outputType),
                        outerContext  // If unifying inputs of (a->a)->a and (int->int)->int, need to store a:=int
                    )
                }  // TODO think about variable shadowing. I think a->(a->a) is fine! what about unifying a-> (a->b) if they have diff names. should each type just have disjoint sets of variables?
                is Node, Error -> err(map)
                is TypeHole -> Pair(a, map)
            }
        }
        is Node -> when (b) {
            is Variable -> unifyVar(b, a, map)
            is Node -> {
                if (a.label != b.label || a.typeParams.size != b.typeParams.size) err(map)
                var currMap = map
                val (params, maps) = (0 until a.typeParams.size).map {
                    val (param, newMap) = unify(a.typeParams[it], b.typeParams[it], currMap)
                    currMap = newMap
                    Pair(param, newMap)
                }.unzip()
                if (Error in params) {
                    val e = params.indexOf(Error)
                    // If we failed in the middle, return the map causing the error
                    err(if (e == 0) map else maps[e - 1])
                }
                // If unifying first param of dict(a,b)->a with dict(int,bool)->int, need to keep a:=int to unify output
                Pair(Node(a.label, params), currMap)
            }
            is Function, Error -> err(map)
            is TypeHole -> Pair(a, map)
        }
        Error -> err(map)
        is TypeHole -> Pair(b, map)
    }

    private fun apply(f: Function, arg: Type, map: Context): Pair<Type, Context> {
        val (specializedF, fnContext) = unify(f.param, arg, map)
        if (specializedF is Error) return err(fnContext)
        return resolve((specializedF as Function).out, fnContext)
    }

    // Notice it's similar to unify
    /** Should never produce new errors */
    private fun resolve(t: Type, map: Context): Pair<Type, Context> = when (t) {
        Error -> err(map)
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
            assert (Error !in params)  // TODO I think this is right..
            Pair(Node(t.label, params), currMap)
        }
    }
}
