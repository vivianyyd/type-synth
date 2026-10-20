package query

import util.lines

/**
 * A program: a Hindley-Milner term over the named components being typed.
 *
 * A [Name] is any variable reference. It refers to the nearest enclosing [Lam] or [Let] that binds
 * it, and to a component if there is none, so a binder shadows a component of the same name.
 * [names] are the components a program uses, which are its free names. Two programs are equal when
 * they are the same up to renaming bound names, so `fun x -> x` equals `fun y -> y`.
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

    /**
     * This with each let's name replaced by its value, so it has no lets.
     *
     * If this type-checks, so does the result: `let x = v in b` type-checks exactly when v and
     * `b[v/x]` do. The converse fails when a let's name is unused, since its value is dropped. So
     * this is for positive examples only.
     */
    fun inlineLets(): Example =
        when (this) {
            is Name -> this
            is App -> App(fn.inlineLets(), arg.inlineLets())
            is Lam -> Lam(param, body.inlineLets())
            is Let -> body.inlineLets().substitute(name, value.inlineLets())
        }

    /**
     * This with [value] in place of each free use of [name]. A binder that would capture one of
     * [value]'s names is renamed first.
     */
    fun substitute(name: String, value: Example): Example =
        when (this) {
            is Name -> if (this.name == name) value else this
            is App -> App(fn.substitute(name, value), arg.substitute(name, value))
            is Lam ->
                when (param) {
                    name -> this
                    in value.names -> {
                        val fresh = freshName(param, value.names + body.names)
                        Lam(fresh, body.substitute(param, Name(fresh)).substitute(name, value))
                    }
                    else -> Lam(param, body.substitute(name, value))
                }
            is Let -> {
                val newValue = this.value.substitute(name, value)
                when (this.name) {
                    name -> Let(this.name, newValue, body)
                    in value.names -> {
                        val fresh = freshName(this.name, value.names + body.names)
                        Let(fresh, newValue, body.substitute(this.name, Name(fresh)).substitute(name, value))
                    }
                    else -> Let(this.name, newValue, body.substitute(name, value))
                }
            }
        }
}

/** [base] with a number added, so that it is not in [taken]. */
private fun freshName(base: String, taken: Set<String>): String =
    generateSequence(1) { it + 1 }.map { "$base$it" }.first { it !in taken }

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

    private val key by lazy { alphaKey(this) }

    override fun equals(other: Any?) = other is Lam && key == other.key

    override fun hashCode() = key.hashCode()
}

/**
 * `let name = value in body`. Not recursive: [name] is bound in [body] only. In Hindley-Milner,
 * [name] is generalized, so [body] may use it at different types.
 */
data class Let(val name: String, val value: Example, val body: Example) : Example {
    override fun toString() = "let $name = $value in $body"

    override val names by lazy { value.names + (body.names - name) }

    private val key by lazy { alphaKey(this) }

    override fun equals(other: Any?) = other is Let && key == other.key

    override fun hashCode() = key.hashCode()
}

/**
 * [e] with each bound name replaced by how many binders out its own is (its de Bruijn index), so
 * that two examples have equal keys exactly when they are the same up to renaming bound names.
 * [bound] are the names bound around [e], innermost last.
 */
private fun alphaKey(e: Example, bound: List<String> = emptyList()): Any =
    when (e) {
        is Name ->
            bound.lastIndexOf(e.name).let { if (it < 0) e.name else BoundKey(bound.lastIndex - it) }
        is App -> AppKey(alphaKey(e.fn, bound), alphaKey(e.arg, bound))
        is Lam -> LamKey(alphaKey(e.body, bound + e.param))
        is Let -> LetKey(alphaKey(e.value, bound), alphaKey(e.body, bound + e.name))
    }

// A free name's key is the name itself, a String, so it is never equal to one of these.
private data class BoundKey(val index: Int)

private data class AppKey(val fn: Any, val arg: Any)

private data class LamKey(val body: Any)

private data class LetKey(val value: Any, val body: Any)

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

    // Lets are inlined, so that a component applied under a let-bound name, as in
    // `let f = cons in f x l`, is flat as `cons x l`.
    private val flatPos by lazy { flat(posWithSubexprs.map { it.inlineLets() }.distinct()) }
    private val flatNeg by lazy { flat(neg) }

    fun flatPos(name: String) = flatPos[name] ?: listOf()

    fun flatNeg(name: String) = flatNeg[name] ?: listOf()

    /** Leaves out the examples that are not a component applied to arguments. See [flatten]. */
    private fun flat(exs: Collection<Example>) = exs.mapNotNull { it.flatten() }.groupBy { it.name }

    override fun toString() = "Pos\n" + posWithSubexprs.lines() + "\n" + "Neg\n" + neg.lines()
}
