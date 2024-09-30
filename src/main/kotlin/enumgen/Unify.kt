package enumgen

typealias Context = MutableMap<Variable, Type>

fun err(map: Context) = Pair(Error, map)

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
            }
        }
        is Function -> {
            when (b) {
                is Variable -> unifyVar(b, a, map)
                is Function -> {
                    val (param, innerContext) = unify(a.param, b.param, map)
                    val (outputType, outerContext) = unify(a.out, b.out, innerContext)
                    Pair(
                        Function(param, outputType),
                        outerContext  // If unifying inputs of (a->a)->a and (int->int)->int, need to store a:=int
                    )
                }  // TODO think about variable shadowing. I think a->(a->a) is fine! what about unifying a-> (a->b) if they have diff names. should each type just have disjoint sets of variables?
                is Node, Error -> err(map)
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
        }
        Error -> err(map)
    }
}
