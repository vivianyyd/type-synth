package symbolicgen

import util.App
import util.Example
import util.NewQuery
import util.subexprs

typealias Port = TODO("set(parent union V union L)??")

class SymbolicTypeBuilder(val query: NewQuery) {


    private fun readPosApp(ex: App) {

        TODO()
    }

    private fun readNegApp(ex: App) {
        TODO()
    }

    fun readAllExamples() {
        query.posExamples.filterIsInstance<App>().flatMap { it.subexprs() }.forEach { readPosApp(it) }
        query.negExamples.filterIsInstance<App>()
            ./*TODO do analysis to localize errors based on posexs when possible*/forEach { readNegApp(it) }
    }
}
