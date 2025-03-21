package symbolicgen

import util.App
import util.Example
import util.NewQuery
import util.subexprs
import java.util.function.Predicate

sealed interface Choice
data class Port(val f: Function, val side: Int) : Choice
data class Root(val name: String) : Choice

class State {
    private val state: Map<String, MutableList<SymbolicType>> = mapOf()

    /** Kind of like [check(ex)], but returns a set of possible types based on the current state */
    fun exprToChoice(ex: Example): Choice = TODO()

    fun param(choice: Choice): Choice = TODO()

    private fun options(choice: Choice) = when (choice) {
        is Port -> if (choice.side == 0) choice.f.left else choice.f.rite
        is Root -> state[choice.name]!!
    }

    fun empty(choice: Choice) = options(choice).isEmpty()

    fun prune(choice: Choice, predicate: Predicate<SymbolicType>) {
        assert(!empty(choice))
        options(choice).removeAll { predicate.test(it) }
        if (empty(choice)) throw Exception("UNSAT!")  // TODO Somebody needs to catch this
    }

    private fun allOptions(parent: Parent?) = listOf(Variable(parent), Label(parent), Function(parent = parent))

    fun addAll(choice: Choice) {
        val parent = when (choice) {
            is Port -> Parent(choice.f, choice.side)
            is Root -> null
        }
        options(choice).addAll(allOptions(parent).filter {
            it !in options(choice) &&
                    /* micro-optimization */ (choice !is Root || it !is Variable)
        })
    }
}

class SymbolicTypeBuilder(val query: NewQuery) {
    val s = State()

    private fun mustBeFn(fn: Example) {
        val choice = s.exprToChoice(fn)
        val prune = { t: SymbolicType -> !(t is Function || t is Variable) }
        if (s.empty(choice)) s.addAll(choice)
        s.prune(choice, prune)
    }

    private fun validArg(fn: Example, arg: Example) {
        val lhs = s.exprToChoice(arg)
        val rhs = s.param(s.exprToChoice(fn))
        // lhs <=u rhs
        TODO()
    }

    private fun readPosApp(ex: App) {
        mustBeFn(ex.fn)
        validArg(ex.fn, ex.arg)
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
