package query

import enumgen.Assignment
import types.*
import types.Function

fun check(ex: Example, context: Assignment): Type? = when (ex) {
    is Name -> context[ex.name]!!
    is App -> when (val f = check(ex.fn, context)) {
        is Function -> check(ex.arg, context)?.let { apply(f, it) }
        null, is LabelNode, is Variable -> null
        is TypeHole, is Error -> throw Exception("how")
    }
}
