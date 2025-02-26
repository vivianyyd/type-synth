package enumgen.types

import enumgen.*
import util.Application

fun checkApplication(app: Application, map: Assignment): Type {
    var fn = map[app.name] ?: throw Exception("Function name not found")
    app.arguments.forEach { arg -> fn = Unify.apply(fn, checkApplication(arg, map)) }
    return fn
}
