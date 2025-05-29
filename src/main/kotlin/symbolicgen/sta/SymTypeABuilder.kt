package symbolicgen.sta

import util.*
import java.util.function.Predicate

sealed interface Choice
data class Port(val f: Function, val side: Int) : Choice
data class Root(val name: String) : Choice

class State(query: Query) {
    private val state: Map<String, MutableList<SymTypeA>> = query.names.associateWith { mutableListOf() }

    /** Replace the entire subtree rooted at [name]. Use with caution.
     * TODO: This is only intended for manually setting nullaries to Label; make this nicer encapsulated later */
    fun plant(name: String, types: List<SymTypeA>) {
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

    fun options(choice: Choice) = when (choice) {
        is Port -> if (choice.side == 0) choice.f.left else choice.f.rite
        is Root -> state[choice.name]!!
    }

    fun singleton(choice: Choice): SymTypeA? {
        val l = options(choice)
        return if (l.size == 1) l[0] else null
    }

    private fun empty(choice: Choice) = options(choice).isEmpty()

    /**  Ensure the options for [choice] are a subset of types satisfying [predicate].
     * If options for [choice] are empty/not yet enumerated, populates them. */
    fun ensureSubset(choice: Choice, predicate: Predicate<SymTypeA>) {
        if (empty(choice)) addAll(choice)
        prune(choice, predicate.negate())
    }

    private fun prune(choice: Choice, predicate: Predicate<SymTypeA>) {
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

    fun read(): Map<String, List<SymTypeA>> = state
}

class SymTypeABuilder(val query: Query) {
    private val s = State(query)

    val make: State by lazy {
        readAllExamples()
        patchEmptyLists()
        s
    }

    private inline fun <reified R> List<*>.singleton(): Boolean = this.size == 1 && this[0] is R

    private fun antiunify(trees: List<List<SymTypeA>>, param: List<SymTypeA>): List<SymTypeA> {
        // TODO intersect stuff with param to produce the new param tree
        if (trees.size == 1) return trees[0]
        if (trees.any { it.singleton<Hole>() }) return antiunify(
            trees.filter { !(it.size == 1 && it[0] is Hole) },
            param
        )
        if (trees.any { it.singleton<Function>() } && trees.any { it.singleton<Label>() }) listOf(Variable())
//        if (trees.all { it.singleton<Label>() }) return listOf(
//            Variable(),
//            Label()
//        )  // TODO should we keep variable here
        // no-op / bottom. could compare equality to guarantee is L instead of V but let's not

        // au(_, (v+_)) = bottom
        // au({l1->r1}, {l2->r2}, ...) = au({l1}, {l2}, ...) -> au({r1}, {r2}, ...)
        if (trees.all { it.singleton<Function>() }) {
            return if (param.any { it is Function }) {
                val (fn, notFn) = param.partition { it is Function }
                notFn + Function(
                    antiunify(trees.map { (it[0] as Function).left }, (fn[0] as Function).left).toMutableList(),
                    antiunify(trees.map { (it[0] as Function).rite }, (fn[0] as Function).rite).toMutableList()
                )

            } else param + Function(
                antiunify(trees.map { (it[0] as Function).left }, listOf(Hole())).toMutableList(),
                antiunify(trees.map { (it[0] as Function).rite }, listOf(Hole())).toMutableList()
            )
        }
        return param // TODO
    }

    fun deepen(): State {
        // TODO can AU outputs too but for now just do inputs
        val paramToArgs = mutableMapOf<Choice, MutableSet<Choice>>()
        fun add(param: Choice, arg: Choice) {
            if (param in paramToArgs) paramToArgs[param]!!.add(arg) else paramToArgs[param] = mutableSetOf(arg)
        }
        query.posExamples.filterIsInstance<App>().forEach { (fn, arg) ->
            val f = s.exprToChoice(fn)
            val a = s.exprToChoice(arg)
            if (f != null && a != null) {
                val p = s.param(f)
                p?.let { add(p, a) }
            }
        }

        paramToArgs.forEach { (param, args) ->
            antiunify(args.map { s.options(it) }, s.options(param))

            // antiunify arguments, then use it to fill in param - second step is not quite antiunif?
            // actual type should be intersected with result of au unless hole then = returned thing and unless fn
            // then recurse??

            TODO()
        }
        // the choice for param MUST permit AT LEAST ONE of the subtrees for arg (if hole, expand to permit all)

        query.negExamples.forEach {
            // the choice for param CAN'T permit at least one of the subtrees for arg
//               ^ that's too strong, we don't have to deal with negexs if we don't want to
        }
        TODO()
    }

    private fun patchEmptyLists() {
        fun patch(t: SymTypeA, rightmost: Boolean) {
            when (t) {
                is Function -> {
                    if (t.left.isEmpty()) t.left.add(Hole())
                    else t.left.map { patch(it, false) }
                    if (t.rite.isEmpty()) {
                        if (rightmost) t.rite.add(Hole())
                        else t.rite.add(Hole())
                    } else t.rite.map { patch(it, rightmost) }
                }
                is Label, is Variable, is Hole -> return
            }
        }
        query.names.forEach { n ->
            val options = s.read()[n]!!
            if (options.isEmpty()) s.plant(n, listOf(Hole()))
            options.forEach { patch(it, true) }
        }
    }

    private fun mustBeFn(fn: Example) {
        val choice = s.exprToChoice(fn) ?: return
        s.ensureSubset(choice) { t: SymTypeA -> t is Function || t is Variable }
    }

    private fun validArg(fn: Example, arg: Example) {
        val lhs = s.exprToChoice(arg) ?: return
        val rhs = s.exprToChoice(fn)?.let { s.param(it) } ?: return

        val lhsSingle = s.singleton(lhs)
        val rhsSingle = s.singleton(rhs)

        if (lhsSingle is Label) s.ensureSubset(rhs) { t: SymTypeA -> t is Label || t is Variable }
        if (lhsSingle is Function) s.ensureSubset(rhs) { t: SymTypeA -> t is Function || t is Variable }
        // TODO IS IT TRUE THAT IF RHS IS LABEL, LHS CAN'T BE VAR?
        if (rhsSingle is Label) s.ensureSubset(lhs) { t: SymTypeA -> t is Label }
        if (rhsSingle is Function) s.ensureSubset(lhs) { t: SymTypeA -> t is Function }
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

    SymTypeABuilder(query).make.printState()
}
/* {cons=[[V, L] -> [V, [V, L] -> []]], 0=[L], []i=[L]} */