package types

import query.FlatApp

typealias Context = MutableMap<Variable, Type>

// TODO throughout this file need to make consistent which context gets returned with Errors
object OldUnify {
    /** Assumes [target] is not a variable with an entry in [map]. */
    private fun unifyVar(v: Variable, target: Type, map: Context): Pair<Type, Context> =
        map[v]?.let { unify(it, target, map) } ?: run {
            if (target is Variable) {
                val cmp = v.id.compareTo(target.id)
                if (cmp < 0) {
                    map[v] = target
                    Pair(target, map)
                } else if (cmp == 0) Pair(target, map) // TODO idk if this is right
                else {
                    map[target] = v
                    Pair(v, map)
                }
            } else {
                if (containsVar(v, target, map)) Pair(
                    Error(v, target, ErrorCategory.VAR_REFERENCES_SELF),
                    map
                )  // TODO think about examples that get us here
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
                is LabelNode -> Pair(Error(b, a, ErrorCategory.PASSED_LABEL_AS_FN), map)
                is Error -> Pair(b, map)
                is TypeHole -> Pair(a, map)
            }
        }
        is LabelNode -> when (b) {
            is Variable -> unifyVar(b, a, map)
            is LabelNode -> {
                if (a.label != b.label) Pair(Error(a, b, ErrorCategory.LABEL_MISMATCH), map)
                else if (a.params.size != b.params.size)
                    Pair(Error(a, b, ErrorCategory.PARAM_QUANTITY_MISMATCH), map)
                else {
                    var currMap = map
                    var error: Pair<Type, Context>? = null
                    val params = a.params.indices.map {
                        val (param, newMap) = unify(a.params[it], b.params[it], currMap)
                        if (param is Error && error == null) error = Pair(param, currMap)
                        currMap = newMap
                        param
                    }
                    error ?: Pair(LabelNode(a.label, params), currMap)
                }
            }
            is Function -> Pair(Error(a, b, ErrorCategory.PASSED_FN_AS_LABEL), map)
            is Error -> Pair(b, map)
            is TypeHole -> Pair(a, map)
        }
        is Error -> Pair(a, map)
        is TypeHole -> Pair(b, map)
    }

    fun unifies(a: Type, b: Type): Boolean {
        val tmp = unify(a, b, mutableMapOf()).first
        return tmp !is Error
    }

    fun apply(f: Type, arg: Type): Type {
        // TODO figure out what to output if f is a hole. alternatively just always enum functions first but sometimes cyclic
        if (f is TypeHole) return f
        if (f !is Function) return Error(f, arg, ErrorCategory.APPLIED_NON_FUNCTION)
        val (parameter, fnContext) = unify(f.left, arg, mutableMapOf())
        if (parameter is Error) return parameter
        return resolve(f.rite, fnContext).first
    }

    // Notice it's similar to unify
    /** Should never produce new errors */
    private fun resolve(t: Type, map: Context): Pair<Type, Context> {
        return when (t) {
            is Error -> Pair(t, map)
            is TypeHole -> Pair(t, map)
            is Variable -> map[t]?.let { resolve(it, map) } ?: Pair(t, map)
            // TODO ^ I think we want to keep variables not in the Context, instead of throwing an error
            //  but actually maybe it's ok bc the very rhs should never be a plain fresh var?
            is Function -> {
                val (inT, inMap) = resolve(t.left, map)
                val (outT, outMap) = resolve(t.rite, inMap)
                // TODO check for error in inT, outT
                Pair(Function(inT, outT), outMap)
            }
            is LabelNode -> {
                var currMap = map
                val params = (0 until t.params.size).map {
                    val (param, newMap) = resolve(t.params[it], currMap)
                    currMap = newMap
                    param
                }
                assert(params.none { it is Error })
                Pair(LabelNode(t.label, params), currMap)
            }
        }
    }
}

fun checkApplication(app: FlatApp, map: Assignment): Type {
    var fn = map[app.name] ?: throw Exception("Function name not found")
    app.args.forEach { arg -> fn = OldUnify.apply(fn, checkApplication(arg, map)) }
    return fn
}
