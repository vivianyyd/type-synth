package enumgen.types

import enumgen.Assignment
import util.FlatApp

fun checkApplication(app: FlatApp, map: Assignment): Type {
    var fn = map[app.name] ?: throw Exception("Function name not found")
    app.args.forEach { arg -> fn = Unify.apply(fn, checkApplication(arg, map)) }
    return fn
}
