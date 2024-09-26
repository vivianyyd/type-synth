package enumgen

typealias Context = MutableMap<Variable, Type>

fun err(map: Context) = Pair(Error, map)

class Unify {
    private fun unifyVar(v: Variable, target: Type, map: Context): Pair<Type, Context> =
        map[v]?.let { unify(it, target, map) } ?: run {
            map[v] = target
            Pair(target, map)
        }

    private fun unify(a: Type, b: Type, map: Context): Pair<Type, Context> = when (a) {
        is Variable -> {
            when (b) {
                is Variable -> { // Unwrap b if possible
                    // TODO check if this unwrapping is right
                    map[b]?.let { unify(it, a, map) } ?: unifyVar(a, b, map)
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
                    val output = unify(a.out, b.out, innerContext)
                    Pair(Function(param, output.first), map)  // TODO check this is the correct context to return
                }
                is Node, Error -> err(map)
            }
        }
        is Node -> when (b) {
            is Variable -> unifyVar(b, a, map)
            is Node -> {
                if (a.label != b.label || a.typeParams.size != b.typeParams.size) err(map)
                else {
                    for (i in 0 until a.typeParams.size) {
                        // params should be independent, so the var map shouldn't change between them
                        // TODO think about variable binding here more
                        val (child, _) = unify(a.typeParams[i], b.typeParams[i], map)
                        when (child) {
                            Error -> err(map)
                            else -> {}
                        }
                    }
                    // TODO we actually have to make a new type containing all the results of unifying the children
                    Pair(a, map)
                }
            }
            is Function, Error -> err(map)
        }
        Error -> err(map)
    }
}
