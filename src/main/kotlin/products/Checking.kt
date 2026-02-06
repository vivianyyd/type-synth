package products

import products.types.Function
import products.types.apply
import query.App
import query.Example
import query.Name

fun check(ex: Example, context: products.types.Assignment): products.types.Type? =
    when (ex) {
        is Name -> {
            if (ex.name !in context) throw Exception("${ex.name} not assigned to a type")
            context[ex.name]!!
        }
        is App ->
            when (val f = check(ex.fn, context)) {
                is Function -> check(ex.arg, context)?.let { apply(f, it) }
                null,
                is products.types.LabelNode,
                is products.types.Variable -> null
                is products.types.TypeHole,
                is products.types.Error -> throw Exception("how")
            }
    }
