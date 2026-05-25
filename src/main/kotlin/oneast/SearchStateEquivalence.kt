package oneast

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
fun SearchState.equivalentTo(other: SearchState): Boolean {
    if (this.names.keys != other.names.keys) return false
    val labelMap = HashMap<Int, Int>()
    val labelMapRev = HashMap<Int, Int>()
    for (name in this.names.keys) {
        val t1 = this.types[this.names.getValue(name)]
        val t2 = other.types[other.names.getValue(name)]
        val varMap = HashMap<Int, Int>()
        val varMapRev = HashMap<Int, Int>()
        if (!matchTypes(t1, t2, labelMap, labelMapRev, varMap, varMapRev)) return false
    }
    return true
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
