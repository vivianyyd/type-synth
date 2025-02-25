package enumgen.types

import examplegen.ExampleGenerator
import util.Application
import util.SExprParser

sealed interface Skeleton

data class TypeVar(val app: Application) : Skeleton {
    override fun toString(): String = app.toString()
}

data class Arrow(val left: Skeleton, val rite: Skeleton) : Skeleton {
    override fun toString(): String = "($left -> $rite)"
}

class ArrowSkeleton(val posExamples: List<Application>, val names: List<String>) {
    private fun allSubexprs(): List<Application> {
        fun subexprs(app: Application): List<Application> =
            if (app.arguments == null || app.arguments.isEmpty()) listOf(app)
            else subexprs(  // partial application
                Application(
                    app.name,
                    app.arguments.dropLast(1)
                )
            ) + subexprs(app.arguments.lastOrNull()!!) + listOf(app)
        return posExamples.flatMap { subexprs(it) }
    }

    /** Argument helps reuse some work hackily */
    private fun allTypeVars(subexprs: List<Application> = allSubexprs()): Map<Application, TypeVar> =
        subexprs.associateWith { TypeVar(it) }

    /** Use me carefully */
    private fun <K, V> Map<K, V>.at(key: K): V = this[key]!!

    private fun constraints(): List<Pair<Skeleton, Skeleton>> {
        val subexprs = allSubexprs()
        val vars = allTypeVars(subexprs)
        val constraints = mutableListOf<Pair<Skeleton, Skeleton>>()
        subexprs.forEach { app ->
            if (app.arguments != null && app.arguments.isNotEmpty()) {
                constraints.add(
                    Pair(
                        vars.at(Application(app.name, app.arguments.dropLast(1))),
                        Arrow(left = vars.at(app.arguments.lastOrNull()!!), rite = vars.at(app))
                    )
                )
            }
        }
        return constraints
    }

    private fun occurs(x: TypeVar, t: Skeleton): Boolean = when (t) {
        is TypeVar -> x == t
        is Arrow -> occurs(x, t.left) || occurs(x, t.rite)
    }

    /** Substitute [replacement] for all occurrences of [x] in [t] */
    private fun substitute(replacement: Skeleton, x: TypeVar, t: Skeleton): Skeleton =
        when (t) {
            is TypeVar -> if (x == t) replacement else t
            is Arrow -> Arrow(left = substitute(replacement, x, t.left), rite = substitute(replacement, x, t.rite))
        }

    private fun apply(t: Skeleton, sub: Substitution): Skeleton {
        var term = t
        sub.forEach { (x, u) -> term = substitute(u, x, term) }  // apply left to right; in h::t prepend we fold right
        return term
    }

    private fun unifyOne(s: Skeleton, t: Skeleton): Substitution =
        when {
            s is TypeVar && t is TypeVar -> if (s == t) listOf() else listOf(s to t)
            s is Arrow && t is Arrow -> unify(listOf(Pair(s.left, t.left), Pair(s.rite, t.rite)))
            s is TypeVar && t is Arrow -> if (occurs(s, t)) throw Exception("Unify cyclic") else listOf(s to t)
            s is Arrow && t is TypeVar -> if (occurs(t, s)) throw Exception("Unify cyclic") else listOf(t to s)
            else -> throw Exception("Impossible")
        }

    private fun unify(constraints: List<Pair<Skeleton, Skeleton>>): Substitution {
        val substitution = mutableListOf<Pair<TypeVar, Skeleton>>()
        for ((s, t) in constraints) {
            substitution.addAll(unifyOne(apply(s, substitution), apply(t, substitution)))
        }
        return substitution
    }

    fun unifyAll(): Substitution = unify(constraints())
    /*
    TODO How to find HOFs? I think we can't figure it out until later... So we still have to enum fns
        b/c the fn could be result of partial app?
        Or put(partial app) followed by get()

        HOF if the argument is always a function in all examples. Needs to be iterative process?
        Consider f: (a -> b) -> (a -> b) = (a -> b) -> a -> b
          It's actually wrong to prune the last arrow even if the output is never applied, if we see
          something like f(f(g)) where g is always a function. Since we don't always know that g is a function
          for sure yet, it's definitely wrong to prune the last arrow just because it's unused
          For this example we would probably conclude f is a->a; if the argument is always a function
          which type do we prefer?

        Something is only l[a->b] if it's an l[a] with arrow substituted for a. Otherwise
        if there's something like make: a -> b -> l[a->b] and destruct: l[a->b] -> (a->b)
        It's indistinguishable from make: a -> b -> l[a,b] and destruct: l[a,b] -> (a->b)
     */
}

fun contain(term: Skeleton, pattern: Skeleton): Boolean {
    if (term == pattern) return true
    return when (term) {
        is TypeVar -> {
            false
//            fun contains(app: Application, pat: Application): Boolean =
//                if (app == pat) true else app.arguments?.any { contains(it, pat) } ?: false
//            contains(term.app, pattern)
        }
        is Arrow -> contain(term.left, pattern) || contain(term.rite, pattern)
    }
}

/** Substitute [replacement] for all occurrences of [x] in [t] */
fun substituteSk(replacement: Skeleton, x: Skeleton, t: Skeleton): Skeleton {
    if (t == x) return replacement
    return when (t) {
        is TypeVar -> t
        is Arrow -> Arrow(left = substituteSk(replacement, x, t.left), rite = substituteSk(replacement, x, t.rite))
    }
}

fun main() {
    val groundTruth = listOf(
        "(i)",
        "(b)",
        "(-> a (-> (l a) (l a)))"
    )

//    val (pos, neg, context) = ExampleGenerator.examples(groundTruth.map { tySexpr ->
//        SExprParser(tySexpr).parse().toType()
//    })
//    println(context.toList().joinToString(separator = "\n"))
//    println("Positive examples:")
//    println(pos.size)
//    val names = context.keys

    val a = Application("a", null)
    val f = Application("f", null)
    val g = Application("g", null)
    val h = Application("h", null)

    val pos = listOf(
        a, f, g, h,
        Application("f", listOf(a)),
        Application("g", listOf(f)),
        Application("h", listOf(g)),
    )
    val names = listOf("a", "f", "g", "h")

    val ask = ArrowSkeleton(pos.toList(), names.toList())
    var result = ask.unifyAll().toMutableList()
    var prevResultSize: Int
    do {
        prevResultSize = result.size
        result.filter { it.first.app.arguments != null && it.first.app.arguments!!.isNotEmpty() }
            .forEach { (lhs, rhs) ->
                val containsLHS = result.filter { contain(it.second, lhs) }
                val replaced = containsLHS.map { Pair(it.first, substituteSk(rhs, lhs, it.second)) }
                if (replaced.isNotEmpty()) {
                    result.removeAll { it in containsLHS }
                    result.addAll(replaced)
                    result.removeIf { it.first == lhs }
                }
            }
    } while (result.size < prevResultSize)
    /*
    TODO do the same as above, but substitute fn names.
        If we have
        ((f ), (a -> (f a)))
        ((g ), (f -> (g f)))
        We should see that f appears as a node in the Skeleton for g (only on the LHS! we don't match inside apps)
     */

    println(result.joinToString(separator = "\n"))
    println(result.size)


//    f: a->b / g: a->b / h: a->b But then we might see that g only ever gets f as argument, so then we have
//    g: (a->b)->c and if h only ever gets g then we get h: ((a->b)->c)->d

}

typealias Substitution = List<Pair<TypeVar, Skeleton>>
