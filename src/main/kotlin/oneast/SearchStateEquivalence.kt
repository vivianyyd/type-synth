package oneast

import util.Logger

/**
 * Returns true iff [this] and [other] denote the same state up to:
 *  - bijective renaming of label IDs (global across all types in the state), and
 *  - bijective renaming of variable IDs (local to each individual type tree).
 *
 * All holes (TypeHole / Blank) are treated as equivalent regardless of subtype.
 * The shape and branching structure of the type ASTs must match exactly.
 *
 * Because the renamings are determined by structural parallel traversal, no
 * backtracking is needed: at each node, the only valid extension of the
 * (label / variable) renaming is forced by the corresponding label or variable
 * on the other side.
 */
fun SearchState.equivalentTo(other: SearchState, logger: Logger? = null): Boolean {
    if (this.names.keys != other.names.keys) return false
    val labelMap = HashMap<Int, Int>()
    val labelMapRev = HashMap<Int, Int>()
    var equivalent = true
    for (name in this.names.keys) {
        val t1 = this.types[this.names.getValue(name)]
        val t2 = other.types[other.names.getValue(name)]
        val varMap = HashMap<Int, Int>()
        val varMapRev = HashMap<Int, Int>()
        if (!matchTypes(t1, t2, labelMap, labelMapRev, varMap, varMapRev)) {
            if (logger == null) return false
            else {
                logger.log("Mismatch for $name: $t1 and $t2")
                equivalent = false
            }
        }
    }
    return equivalent
}

fun equalInEmptyLabelContext(a: ConstraintTy, b: ConstraintTy): Boolean {
    fun ConstraintTy.toNode(): Type =
        when (this) {
            is ConstraintArrow -> Arrow(this.l.toNode(), this.r.toNode())
            is ConstraintLabel -> NamedLabel(this.label, this.params.map { it.toNode() })
            is ConstraintVariable -> Variable(this.v)
            is InstantiationTy -> TypeHole()
        }
    return matchTypes(a.toNode(), b.toNode(), HashMap(), HashMap(), HashMap(), HashMap())
}

private fun matchTypes(
    t1: Type,
    t2: Type,
    labelMap: MutableMap<Int, Int>,
    labelMapRev: MutableMap<Int, Int>,
    varMap: MutableMap<Int, Int>,
    varMapRev: MutableMap<Int, Int>
): Boolean = when {
    t1 is THole && t2 is THole -> true
    t1 is Variable && t2 is Variable -> bindBijective(t1.v, t2.v, varMap, varMapRev)
    t1 is Arrow && t2 is Arrow ->
        matchTypes(t1.l, t2.l, labelMap, labelMapRev, varMap, varMapRev) &&
            matchTypes(t1.r, t2.r, labelMap, labelMapRev, varMap, varMapRev)
    t1 is NamedLabel && t2 is NamedLabel ->
        t1.params.size == t2.params.size &&
            bindBijective(t1.label, t2.label, labelMap, labelMapRev) &&
            t1.params.zip(t2.params).all { (p1, p2) ->
                matchTypes(p1, p2, labelMap, labelMapRev, varMap, varMapRev)
            }
    else -> false
}

private fun bindBijective(
    k: Int,
    v: Int,
    map: MutableMap<Int, Int>,
    mapRev: MutableMap<Int, Int>
): Boolean {
    val existing = map[k]
    if (existing != null) return existing == v
    val existingRev = mapRev[v]
    if (existingRev != null) return false
    map[k] = v
    mapRev[v] = k
    return true
}


/** Total node count: each Variable, Hole, Arrow, and NamedLabel counts as 1. */
fun Type.nodeCount(): Int = when (this) {
    is Variable -> 1
    is THole -> 1
    is Arrow -> 1 + l.nodeCount() + r.nodeCount()
    is NamedLabel -> 1 + params.sumOf { it.nodeCount() }
}

/** Sum of [Type.nodeCount] over every type in the state. */
fun SearchState.nodeCount(): Int = types.sumOf { it.nodeCount() }

/**
 * Cost-based diff between two states, modulo the same renaming semantics as
 * [equivalentTo]: bijective label renaming (global across the state) and
 * bijective variable renaming (local per type).
 *
 * - [cost] is symmetric in expected/actual (subtree sizes don't depend on which
 *   side is which).
 * - [expectedSize] is the total node count of the receiver; used as the
 *   normalization denominator in [ratio].
 *
 * `ratio = cost / expectedSize`, with 0/0 → 0.0 and cost>0/0 → +Inf. The
 * ratio is unbounded: values > 1 mean the actual diverges by more than the
 * expected has nodes (e.g., expected is a hole and actual is a deep tree).
 */
data class StateDiff(val cost: Int, val expectedSize: Int) {
    val ratio: Double = when {
        expectedSize == 0 -> if (cost == 0) 0.0 else Double.POSITIVE_INFINITY
        else -> cost.toDouble() / expectedSize
    }
}

/**
 * @return cost-based diff of [actual] against [this] expected state. See
 *   [StateDiff] for the cost / ratio interpretation. Per-node cost rules:
 *
 * | comparison                                  | cost                          | recurse? |
 * |---------------------------------------------|-------------------------------|----------|
 * | same kind, compatible binding               | 0                             | yes      |
 * | hole vs hole (any THole subtypes)           | 0                             | -        |
 * | variable bijection conflict                 | 1                             | -        |
 * | NamedLabel bijection conflict, same arity   | 1                             | yes      |
 * | NamedLabel arity mismatch                   | nodeCount(t1) + nodeCount(t2) | no       |
 * | kind mismatch (Arrow / Label / Var cross)   | nodeCount(t1) + nodeCount(t2) | no       |
 * | hole vs non-hole                            | nodeCount(non-hole)           | no       |
 *
 * Names appearing on only one side contribute the full nodeCount of that side's
 * tree. Names are processed in sorted order so the (greedy) global label
 * binding is deterministic.
 */
fun SearchState.diffTo(actual: SearchState): StateDiff {
    val labelMap = HashMap<Int, Int>()
    val labelMapRev = HashMap<Int, Int>()
    var cost = 0
    val allNames = (this.names.keys + actual.names.keys).sorted()
    for (name in allNames) {
        val expIdx = this.names[name]
        val actIdx = actual.names[name]
        cost += when {
            expIdx != null && actIdx != null -> {
                val varMap = HashMap<Int, Int>()
                val varMapRev = HashMap<Int, Int>()
                diffTypes(
                    this.types[expIdx], actual.types[actIdx],
                    labelMap, labelMapRev, varMap, varMapRev
                )
            }
            expIdx != null -> this.types[expIdx].nodeCount()
            else -> actual.types[actIdx!!].nodeCount()
        }
    }
    return StateDiff(cost = cost, expectedSize = this.nodeCount())
}

private fun diffTypes(
    t1: Type,
    t2: Type,
    labelMap: MutableMap<Int, Int>,
    labelMapRev: MutableMap<Int, Int>,
    varMap: MutableMap<Int, Int>,
    varMapRev: MutableMap<Int, Int>
): Int = when {
    t1 is THole && t2 is THole -> 0
    t1 is THole -> t2.nodeCount()
    t2 is THole -> t1.nodeCount()
    t1 is Variable && t2 is Variable ->
        if (bindBijective(t1.v, t2.v, varMap, varMapRev)) 0 else 1
    t1 is Arrow && t2 is Arrow ->
        diffTypes(t1.l, t2.l, labelMap, labelMapRev, varMap, varMapRev) +
            diffTypes(t1.r, t2.r, labelMap, labelMapRev, varMap, varMapRev)
    t1 is NamedLabel && t2 is NamedLabel ->
        if (t1.params.size != t2.params.size) t1.nodeCount() + t2.nodeCount()
        else {
            val headCost =
                if (bindBijective(t1.label, t2.label, labelMap, labelMapRev)) 0 else 1
            headCost + t1.params.zip(t2.params).sumOf { (p1, p2) ->
                diffTypes(p1, p2, labelMap, labelMapRev, varMap, varMapRev)
            }
        }
    else -> t1.nodeCount() + t2.nodeCount()
}
