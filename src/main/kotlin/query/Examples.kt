package query

import util.lines

/**
 * A program: a Hindley-Milner term over the named components being typed.
 *
 * A [Name] is any variable reference. It refers to the nearest enclosing [Lam] or [Let] that binds
 * it, and to a component if there is none, so a binder shadows a component of the same name.
 * [names] are the components a program uses, which are its free names.
 */
sealed interface Example {
    /** The free names: the components this uses, not counting names bound inside it. */
    val names: Set<String>

    /** How deeply arguments are nested. A name applied to names has depth 1. */
    fun depth(): Int =
        when (this) {
            is Name -> 0
            is App -> maxOf(fn.depth(), arg.depth() + 1)
            is Lam -> body.depth()
            is Let -> maxOf(value.depth(), body.depth())
        }

    fun size(): Int =
        when (this) {
            is Name -> 1
            is App -> fn.size() + arg.size()
            is Lam -> 1 + body.size()
            is Let -> 1 + value.size() + body.size()
        }

    /**
     * This as a name applied to arguments, or null if what is applied is a lambda or a let.
     * Arguments are kept whole, so they may be anything.
     */
    fun flatten(): FlatApp? =
        when (this) {
            is Name -> FlatApp(name)
            is App -> fn.flatten()?.let { FlatApp(it.name, it.args + arg) }
            is Lam, is Let -> null
        }

    /**
     * All closed subexpressions of [this], including [this]. Each appears before any expression
     * that contains it.
     *
     * A subexpression is closed if it uses no name bound outside it, so it means the same on its
     * own as where it occurs. Only those are programs in their own right: in `fun x -> f x`, the
     * subexpression `f x` is not, because x is bound by the lambda.
     */
    fun subexprs(): List<Example> =
        LinkedHashSet<Example>().also { addClosedSubexprs(emptySet(), it) }.toList()

    private fun addClosedSubexprs(bound: Set<String>, into: MutableSet<Example>) {
        when (this) {
            is Name -> {}
            is App -> {
                fn.addClosedSubexprs(bound, into)
                arg.addClosedSubexprs(bound, into)
            }
            is Lam -> body.addClosedSubexprs(bound + param, into)
            is Let -> {
                value.addClosedSubexprs(bound, into)
                body.addClosedSubexprs(bound + name, into)
            }
        }
        if (names.none { it in bound }) into.add(this)
    }

    /** Whether this contains a [Lam] or a [Let]. */
    fun hasBinders(): Boolean =
        when (this) {
            is Name -> false
            is App -> fn.hasBinders() || arg.hasBinders()
            is Lam, is Let -> true
        }
}

// toString() is OCaml syntax: OCamlChecker type-checks examples by compiling it.

data class Name(val name: String) : Example {
    override fun toString() = name

    override val names by lazy { setOf(name) }
}

data class App(val fn: Example, val arg: Example) : Example {
    override fun toString(): String =
        "${if (fn is Lam || fn is Let) "($fn)" else "$fn"} ${if (arg is Name) "$arg" else "($arg)"}"

    override val names by lazy { fn.names + arg.names }
}

/** `fun param -> body`. Takes one parameter; nest them for more. */
data class Lam(val param: String, val body: Example) : Example {
    override fun toString() = "fun $param -> $body"

    override val names by lazy { body.names - param }
}

/**
 * `let name = value in body`. Not recursive: [name] is bound in [body] only. In Hindley-Milner,
 * [name] is generalized, so [body] may use it at different types.
 */
data class Let(val name: String, val value: Example, val body: Example) : Example {
    override fun toString() = "let $name = $value in $body"

    override val names by lazy { value.names + (body.names - name) }
}

/**
 * This is more general than the previous query because we can apply the result of applications
 * without them being explicitly assigned to a name [posWithSubexprs] contains all subexpressions!
 *
 * @requires [negIn] contains MINIMAL negative examples, i.e. no strict subexpression is a negative example.
 */
class Examples(posIn: Collection<Example>, negIn: Collection<Example>) {
    val posNoSubexprs: List<Example>
    val neg: List<Example> = negIn.toList()

    init {
        val posInSet = posIn.toSet()
        val strictSubexprs = buildSet {
            // subexprs() ends with the ex itself
            posInSet.forEach { addAll(it.subexprs().dropLast(1)) }
        }
        posNoSubexprs = posInSet.filter { it !in strictSubexprs }
    }

    val posWithSubexprs by lazy {
        buildSet {
            posNoSubexprs.forEach { addAll(it.subexprs()) }
        }.toList()
    }

    val names by lazy {
        buildSet {
            (posNoSubexprs + neg).forEach { addAll(it.names) }
        }.sorted()
    }

    private val flatPos by lazy { flat(posWithSubexprs) }
    private val flatNeg by lazy { flat(neg) }

    fun flatPos(name: String) = flatPos[name] ?: listOf()

    fun flatNeg(name: String) = flatNeg[name] ?: listOf()

    /** Leaves out the examples that are not a component applied to arguments. See [flatten]. */
    private fun flat(exs: Collection<Example>) = exs.mapNotNull { it.flatten() }.groupBy { it.name }

    override fun toString() = "Pos\n" + posWithSubexprs.lines() + "\n" + "Neg\n" + neg.lines()
}
