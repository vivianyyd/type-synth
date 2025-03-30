package symbolicgen

import util.*
import java.util.function.Predicate

sealed interface Choice
data class Port(val f: Function, val side: Int) : Choice
data class Root(val name: String) : Choice

class State(query: NewQuery) {
    private val state: Map<String, MutableList<SymbolicType>> = query.names.associateWith { mutableListOf() }

    /** Replace the entire subtree rooted at [name]. Use with caution.
     * TODO: This is only intended for manually setting nullaries to Label; make this nicer encapsulated later */
    fun plant(name: String, types: List<SymbolicType>) {
        state[name]!!.clear()
        state[name]!!.addAll(types)
    }

    /** Kind of like [check(ex)], but returns a set of possible types based on the current state
     * [null] indicates bottom; we've iterated into a variable and can't get any further information */
    fun exprToChoice(ex: Example): Choice? = when (ex) {
        is Name -> Root(ex.name)
        is App -> {
            val fn = exprToChoice(ex.fn)
            if (fn == null) null
            else {
                val options = options(fn)
                if (!options.any { it is Variable || it is Function }) throw Exception("UNSAT!" + printState())
                options.find { it is Function }?.let { Port(it as Function, 1) }
            }
        }
    }

    fun param(fn: Choice): Choice? {
        val options = options(fn)
        if (!options.any { it is Variable || it is Function }) throw Exception("UNSAT!")
        return options.find { it is Function }?.let { Port(it as Function, 0) }
    }

    private fun options(choice: Choice) = when (choice) {
        is Port -> if (choice.side == 0) choice.f.left else choice.f.rite
        is Root -> state[choice.name]!!
    }

    fun singleton(choice: Choice): SymbolicType? {
        val l = options(choice)
        return if (l.size == 1) l[0] else null
    }

    private fun empty(choice: Choice) = options(choice).isEmpty()

    /**  Ensure the options for [choice] are a subset of types satisfying [predicate].
     * If options for [choice] are empty/not yet enumerated, populates them. */
    fun ensureSubset(choice: Choice, predicate: Predicate<SymbolicType>) {
        if (empty(choice)) addAll(choice)
        prune(choice, predicate.negate())
    }

    private fun prune(choice: Choice, predicate: Predicate<SymbolicType>) {
        assert(!empty(choice))
        options(choice).removeAll { predicate.test(it) }
        // TODO Somebody needs to catch this. Or do something more idiomatic and return special type or boolean
        if (empty(choice)) throw Exception("UNSAT!")
    }

    private fun allOptions(parent: Parent?) = listOf(Variable(parent), Label(parent), Function(parent = parent))

    private fun addAll(choice: Choice) {
        val parent = when (choice) {
            is Port -> Parent(choice.f, choice.side)
            is Root -> null
        }
        options(choice).addAll(allOptions(parent).filter {
            it !in options(choice) &&
                    /* micro-optimization */ (choice !is Root || it !is Variable)
        })
    }

    fun printState() = println(state)

    fun read(): Map<String, List<SymbolicType>> = state
}

class SymbolicTypeBuilder(val query: NewQuery) {
    private val s = State(query)

    val make: State by lazy {
        readAllExamples()
        patchEmptyLists()
        s
    }

    private fun patchEmptyLists() {
        val defaultOptions = listOf(Variable(), Label())
        fun patch(t: SymbolicType) {
            when (t) {
                is Function -> {
                    if (t.left.isEmpty()) t.left.addAll(defaultOptions)
                    else t.left.map { patch(it) }
                    if (t.rite.isEmpty()) t.rite.addAll(defaultOptions)
                    else t.rite.map { patch(it) }
                }
                is Label, is Variable -> return
            }
        }
        query.names.forEach { n ->
            val options = s.read()[n]!!
            if (options.isEmpty()) s.plant(n, defaultOptions)
            options.forEach { patch(it) }
        }
    }

    private fun mustBeFn(fn: Example) {
        val choice = s.exprToChoice(fn) ?: return
        s.ensureSubset(choice) { t: SymbolicType -> t is Function || t is Variable }
    }

    private fun validArg(fn: Example, arg: Example) {
        val lhs = s.exprToChoice(arg) ?: return
        val rhs = s.exprToChoice(fn)?.let { s.param(it) } ?: return

        val lhsSingle = s.singleton(lhs)
        val rhsSingle = s.singleton(rhs)

        if (lhsSingle is Label) s.ensureSubset(rhs) { t: SymbolicType -> t is Label || t is Variable }
        if (lhsSingle is Function) s.ensureSubset(rhs) { t: SymbolicType -> t is Function || t is Variable }
        // TODO IS IT TRUE THAT IF RHS IS LABEL, LHS CAN'T BE VAR?
        if (rhsSingle is Label) s.ensureSubset(lhs) { t: SymbolicType -> t is Label }
        if (rhsSingle is Function) s.ensureSubset(lhs) { t: SymbolicType -> t is Function }
        // TODO any other interesting inferences?

        /*
        lhs <= rhs
        INFERENCE RULES:
        rhs is {L} <=> rhs pick L => lhs pick L <=> lhs is {L}
        rhs is {->} <=> rhs pick -> => lhs pick -> <=> lhs is {->}
        Helpful to write in terms of pick, since pick rules are solved for by Sketch?
        lhs is {L} => rhs is L or V (prune anything that isn't)
        lhs is {->} => rhs is -> or V (prune anything that isn't)
         */
    }

    private fun readPosApp(ex: App) {
        mustBeFn(ex.fn)
        validArg(ex.fn, ex.arg)
    }

    private fun readAllExamples() {
        val expandedApps = query.posExamples.filterIsInstance<App>()
        // TODO check if the nullary pass is good, refactor to make it nicer
        query.names.filter {
            expandedApps.none { app -> app.fn is Name && app.fn.name == it }
        }.forEach { s.plant(it, listOf(Label())) }

        expandedApps.forEach { readPosApp(it) }
//        query.negExamples.filterIsInstance<App>()
//            ./*TODO do analysis to localize errors based on posexs when possible*/forEach { readNegApp(it) }
        // TODO do we ever learn anything at this stage from negative examples?
    }
}

fun main() {
    val consExamples = mapOf(
        "(+ 0)" to "int",
        "(+ tr)" to "bool",
        "(+ []i)" to "lint",
        "(+ []b)" to "lbool",
        "(+ [[]]i)" to "llint",
        "(+ (cons 0 []i))" to "lint",
        "(+ (cons 0 (cons 0 []i)))" to "lint",
        "(+ (cons tr []b))" to "lbool",
        "(+ (cons tr (cons tr []b)))" to "lbool",
        "(+ (cons []i [[]]i))" to "llint",
        "(+ (cons []i (cons []i [[]]i)))" to "llint",
        "(- (cons tr []i))" to null,
        "(- (cons []i 0))" to null,
        "(- (cons 0 []b))" to null,
        "(- (cons 0 [[]]i))" to null,
        "(- (cons tr [[]]i))" to null,
        "(- (cons tr (cons 0 []i)))" to null,
    )

    val query = parseNewExamples(consExamples.keys)

    SymbolicTypeBuilder(query).make.printState()
}
/* {cons=[[V, L] -> [V, [V, L] -> []]], 0=[L], []i=[L]} */