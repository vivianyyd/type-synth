package enumgen.types

import examplegen.ExampleGenerator
import util.Application
import util.parseApp

sealed interface Skeleton

data class TypeVar(val app: Application) : Skeleton {
    override fun toString(): String = app.toString()
}

data class Arrow(val left: Skeleton, val rite: Skeleton) : Skeleton {
    override fun toString(): String = "${if (left is Arrow) "($left)" else "$left"} -> $rite"
}

object ArrowAnalysis {
    /** Use me carefully */
    private fun <K, V> Map<K, V>.at(key: K): V = this[key]!!

    private fun constraints(posExamples: List<Application>): List<Pair<Skeleton, Skeleton>> {
        fun subexprs(app: Application): List<Application> =
            if (app.arguments.isEmpty()) listOf(app)
            else subexprs(  // partial application
                Application(
                    app.name,
                    app.arguments.dropLast(1)
                )
            ) + subexprs(app.arguments.lastOrNull()!!) + listOf(app)

        val subexprs = posExamples.flatMap { subexprs(it) }
        val vars = subexprs.associateWith { TypeVar(it) }
        val constraints = mutableListOf<Pair<Skeleton, Skeleton>>()
        subexprs.forEach { app ->
            if (app.arguments.isNotEmpty()) {
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

    private fun apply(t: Skeleton, sub: Substitution): Skeleton {
        /** Substitute [replacement] for all occurrences of [x] in [t] */
        fun substitute(replacement: Skeleton, x: TypeVar, t: Skeleton): Skeleton =
            when (t) {
                is TypeVar -> if (x == t) replacement else t
                is Arrow -> Arrow(left = substitute(replacement, x, t.left), rite = substitute(replacement, x, t.rite))
            }

        var term = t
        sub.forEach { (x, u) -> term = substitute(u, x, term) }  // apply left to right; in h::t prepend we fold right
        return term
    }

    private fun unifyOne(s: Skeleton, t: Skeleton): Substitution {
        fun occurs(x: TypeVar, t: Skeleton): Boolean = when (t) {
            is TypeVar -> x == t
            is Arrow -> occurs(x, t.left) || occurs(x, t.rite)
        }
        return when {
            s is TypeVar && t is TypeVar -> if (s == t) listOf() else listOf(s to t)
            s is Arrow && t is Arrow -> unify(listOf(Pair(s.left, t.left), Pair(s.rite, t.rite)))
            s is TypeVar && t is Arrow -> if (occurs(s, t)) throw Exception("Unify cyclic") else listOf(s to t)
            s is Arrow && t is TypeVar -> if (occurs(t, s)) throw Exception("Unify cyclic") else listOf(t to s)
            else -> throw Exception("Impossible")
        }
    }

    private fun unify(constraints: List<Pair<Skeleton, Skeleton>>): Substitution {
        val substitution = mutableListOf<Pair<TypeVar, Skeleton>>()
        for ((s, t) in constraints) {
            substitution.addAll(unifyOne(apply(s, substitution), apply(t, substitution)))
        }
        return substitution
    }

    fun unifyAll(posExamples: List<Application>, propagateEqualities: Boolean): Substitution {
        val unified = unify(constraints(posExamples))
        return if (propagateEqualities) propagateEqualities(unified) else unified
    }

    private fun propagateEqualities(s: Substitution): Substitution {
        fun contain(term: Skeleton, pattern: Skeleton): Boolean {
            if (term == pattern) return true
            return when (term) {
                is TypeVar -> false
                is Arrow -> contain(term.left, pattern) || contain(term.rite, pattern)
            }
        }

        /** Substitute [replacement] for all occurrences of [x] in [t] */
        fun replace(replacement: Skeleton, x: Skeleton, t: Skeleton): Skeleton {
            if (t == x) return replacement
            return when (t) {
                is TypeVar -> t
                is Arrow -> Arrow(left = replace(replacement, x, t.left), rite = replace(replacement, x, t.rite))
            }
        }

        fun shapeEqual(a: Skeleton, b: Skeleton): Boolean = when (a) {
            is Arrow -> when (b) {
                is Arrow -> shapeEqual(a.left, b.left) && shapeEqual(a.rite, b.rite)
                is TypeVar -> false
            }
            is TypeVar -> when (b) {
                is Arrow -> false
                is TypeVar -> true
            }
        }

        val result = s.toMutableList()
        var prevResultSize: Int
        do {
            prevResultSize = result.size
            result.map { it /* avoid ConcurrentModificationException... */ }.forEach { (lhs, rhs) ->
                fun removeThisPair() =
                    result.removeIf { it.first == lhs && it.second == rhs && it.first.app.arguments.isNotEmpty() }
                if (shapeEqual(lhs, rhs)) removeThisPair() // If they have the same shape, don't bother
                else {
                    val containsLHS = result.filter { contain(it.second, lhs) }
                    val replaced = containsLHS.map { Pair(it.first, replace(rhs, lhs, it.second)) }
                    if (replaced.isNotEmpty()) {
                        result.removeAll { it in containsLHS }
                        result.addAll(replaced)
                        removeThisPair()
                    }
                }
            }
        } while (result.size < prevResultSize)
        return result
    }

    fun unifyToTypes(
        posExamples: List<Application>,
        names: List<String>,
        propagateEqualities: Boolean
    ): Map<String, Type> {
        fun skeletonToType(s: Skeleton): Type = when (s) {
            is Arrow -> Function(skeletonToType(s.left), skeletonToType(s.rite))
            is TypeVar -> ChildHole()
        }

        val unified = unifyAll(posExamples, propagateEqualities)
        return names.associateWith { name ->
            val skeleton = unified.find { it.first.app.name == name && it.first.app.arguments.isEmpty() }
            if (skeleton == null) ChildHole()  // [name] is unconstrained. TODO if completely unconstrained, can we actually make it a variable here?
            else skeletonToType(skeleton.second)
        }
    }
}

fun main() {
    val types = listOf("(i)", "(b)", "(-> a (-> (l a) (l a)))")
    val (query, context) = ExampleGenerator(2, 2, 30, types.map { parseType(it) }).examples()
    val pos = query.posExamples
    println(context.toList().joinToString(separator = "\n"))

//    val pos = listOf("a", "f", "g", "(g a)", "(f g)", "(f (f g))").map { parseApp(it) }

//    val pos = listOf("a", "f", "g", "h", "(f a)", "(g f)", "(h g)").map{parseApp(it)}

    val names = pos.filter { it.arguments.isEmpty() }.map { it.name }
    println(
        ArrowAnalysis.unifyAll(pos.toList(), propagateEqualities = true)
            .joinToString(separator = "\n") { (a, b) -> "$a := $b" })
    println()
    val result = ArrowAnalysis.unifyToTypes(pos.toList(), names, propagateEqualities = true)
    println(result.toList().joinToString(separator = "\n") { (a, b) -> "$a := $b" })
}

// TODO Change to a Map? Does it break substitutions due to ordering or something
typealias Substitution = List<Pair<TypeVar, Skeleton>>
