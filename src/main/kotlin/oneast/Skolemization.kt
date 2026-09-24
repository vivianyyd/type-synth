package oneast

import query.Example
import util.Counter

/**
 * Whether some of [negatives] type-checks in every state the search can still reach from this one,
 * so that none of those can be a solution. Until [labelsSettled], the search can still change
 * labels as well as fill holes.
 */
fun SearchState.acceptsANegative(negatives: List<Example>, labelsSettled: Boolean): Boolean {
    if (negatives.isEmpty()) return false
    val widest = if (labelsSettled) this else uncommittedLabelsAsHoles()
    val hardest = OneUnification(widest.skolemize(), emptyList())
    return negatives.any { hardest.typeChecks(it) }
}

/**
 * This state with each hole replaced by a label of its own, which appears nowhere else, applied to
 * the variables of the type the hole is in.
 *
 * It is the hardest filling there is: a program type-checks however this state's holes are filled
 * if and only if it type-checks in the skolemized state (Theorem 2, refinement stability). So if a
 * negative example type-checks here, nothing the search does by filling holes can reject it.
 * Nothing else is covered: not changing a label's arity, and not turning labels back into blanks.
 * For those, skolemize [uncommittedLabelsAsHoles] instead.
 *
 * Checking against the holes themselves cannot tell. A hole unifies like a fresh variable at each
 * use, which forgets what the hole's type variables were at that use. With
 * `cons : a -> L[a] -> _`, `compare (cons 0 nil) (cons true nil)` type-checks, because the two
 * results are unrelated variables, but it stops type-checking once the hole becomes `L[a]`.
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
    fresh.ensureGt(maxOf(labelArities.keys.maxOrNull() ?: -1, types.maxOfOrNull { it.maxLabel() } ?: -1))
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

/**
 * This state with each label that is not committed, along with its parameters, replaced by a hole
 * of its own.
 *
 * While outlining, the search changes labels without filling holes: it blanks out labels that
 * clash, and it decides label arities afterwards, which rewrites each label's parameters. From
 * this state, every one of those changes is a filling, so [skolemize] still covers them.
 * Committed labels never change, and neither do type variables or arrows.
 */
fun SearchState.uncommittedLabelsAsHoles(): SearchState {
    fun Type.forget(): Type =
        when (this) {
            is Arrow -> Arrow(l.forget(), r.forget())
            is NamedLabel ->
                if (label in committedLabels) copy(params = params.map { it.forget() }) else TypeHole()
            is THole,
            is Variable -> this
        }
    return mapTypes { it.forget() }
}

private fun Type.maxLabel(): Int =
    when (this) {
        is Arrow -> maxOf(l.maxLabel(), r.maxLabel())
        is NamedLabel -> params.fold(label) { max, p -> maxOf(max, p.maxLabel()) }
        is THole,
        is Variable -> -1
    }
