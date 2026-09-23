package oneast

import query.Example
import util.Counter

/**
 * Whether [ex] type-checks however this state's holes are filled, so that nothing the search does
 * below this state can make it stop type-checking. This is what licenses pruning with a negative
 * example.
 *
 * Checking [ex] against the holes themselves cannot tell. A hole unifies like a fresh variable at
 * each use, which forgets what the hole's type variables were at that use. With
 * `cons : a -> L[a] -> _`, `compare (cons 0 nil) (cons true nil)` type-checks, because the two
 * results are unrelated variables, but it stops type-checking once the hole becomes `L[a]`.
 *
 * The [skolemize]d state does not forget, and it is the hardest filling there is: [ex] type-checks
 * under every filling if and only if it type-checks under that one (Theorem 2, refinement
 * stability).
 *
 * A filling replaces holes, with anything, in any number of steps. Nothing else is covered: not
 * changing a label's arity, and not turning labels back into blanks.
 */
fun SearchState.typeChecksUnderEveryFill(ex: Example): Boolean =
    OneUnification(skolemize(), listOf(ex)).ok

/**
 * This state with each hole replaced by a label of its own, which appears nowhere else, applied to
 * the variables of the type the hole is in.
 *
 * The arguments are what make this the hardest filling. A filling may mention those variables
 * (`a -> _` can become `a -> a`), so what a hole stands for is a function of them. A label unifies
 * only with itself, and then only if its arguments do, so `K[x] = K[y]` demands exactly `x = y`,
 * which is the most that equating any two uses of a filling can demand. A bare `K[]` would demand
 * nothing.
 */
fun SearchState.skolemize(): SearchState {
    // Holes are compared by identity, so this asks whether any one hole is in two types.
    val holes = types.flatMap { it.allHoles().distinct() }
    require(holes.size == holes.toSet().size) {
        "A hole is in two types, so it cannot stand for a function of just one's variables"
    }

    val fresh = Counter()
    fresh.ensureGt((labelArities.keys + types.flatMap { it.labels() }).maxOrNull() ?: -1)
    val skolems = HashMap<THole, NamedLabel>()

    fun Type.skolemize(args: List<Variable>): Type =
        when (this) {
            is Arrow -> Arrow(l.skolemize(args), r.skolemize(args))
            is NamedLabel -> copy(params = params.map { it.skolemize(args) })
            is THole -> skolems.getOrPut(this) { NamedLabel(fresh.get(), args) }
            is Variable -> this
        }

    val skolemized = types.map { it.skolemize(it.variables().sorted().map { v -> Variable(v) }) }
    return SearchState(
        names = names,
        types = skolemized,
        labelArities = labelArities + skolems.values.associate { it.label to it.params.size },
        numCommittedTypes = numCommittedTypes,
        committedLabels = committedLabels
    )
}

private fun Type.labels(): List<Int> =
    when (this) {
        is Arrow -> l.labels() + r.labels()
        is NamedLabel -> listOf(label) + params.flatMap { it.labels() }
        is THole,
        is Variable -> emptyList()
    }
