package symbolicgen.symbolicenumerator

import symbolicgen.*
import symbolicgen.Function
import util.*

class SymbolicEnumerator(
    val query: NewQuery,
    state: State,
    private val oracle: EqualityNewOracle,
) {
    private val state = state.read()

    var freshLabel = 0

    val varTypeIds = query.names.withIndex().associate { (i, n) -> n to i }
    private fun tId(name: String) = varTypeIds[name]!!

    fun enumerateAll(): List<Map<String, EnumeratedSymbolicType>> {
        val all = state.mapValues { (n, options) ->
            options.flatMap { enumerate(it, 0, false, n, false).map { it.first } }
        }.contexts().map { it.toMutableMap() }
        return all.filter(::checkPosExsAndMergeLabels)
    }

    /**
     * checks positive examples, and introduces label equivalences as needed
     */
    private fun checkPosExsAndMergeLabels(context: MutableMap<String, EnumeratedSymbolicType>): Boolean {
        val labelClasses = UnionFind(freshLabel)
        fun check(ex: Example): EnumeratedSymbolicType? = when (ex) {
            is Name -> context[ex.name]!!
            is App -> {
                when (val f = check(ex.fn)) {
                    is VL -> f  // This is not actually the output type! It's a hack but it works
                    !is F -> null
                    else -> check(ex.arg)?.let { apply(f, it, labelClasses) }
                }
            }
        }

        val pass = query.posExamples.all { check(it) != null }
        fun updateLs(t: EnumeratedSymbolicType): EnumeratedSymbolicType = when (t) {
            is F -> F(updateLs(t.left), updateLs(t.rite))
            is L -> L(labelClasses.find(t.label))
            is Var -> t
        }

        if (pass) {
            val newContext = context.mapValues { (_, t) -> updateLs(t) }
            context.putAll(newContext)
        }
        return pass
    }

    private fun enumerate(
        t: SymbolicType, vars: Int, pickedLabel: Boolean, name: String, canBeFresh: Boolean
    ): List<Triple<EnumeratedSymbolicType, Int, Boolean>> = when (t) {
        is Hole -> listOf(Variable(), Label()).flatMap { enumerate(it, vars, pickedLabel, name, canBeFresh) }
        is Function -> {
            val lefts = t.left.flatMap { enumerate(it, vars, pickedLabel, name, true) }
            lefts.flatMap { (left, lvs, lab) ->
                val rites = t.rite.flatMap { enumerate(it, lvs, lab, name, false) }
                rites.map { (rite, rvs, lab) -> Triple(F(left, rite), rvs, lab) }
            }
        }
        is Label -> listOf(Triple(L(freshLabel++), vars, true))
        is Variable -> {
            val variables: MutableList<Triple<EnumeratedSymbolicType, Int, Boolean>> =
                (0 until vars).map { Triple(VR(it, tId(name)), vars, pickedLabel) }.toMutableList()
            if (canBeFresh) variables.add(Triple(VB(vars, tId(name)), vars + 1, pickedLabel))
            else if (pickedLabel) variables.add(Triple(VL(vars, tId(name)), vars + 1, pickedLabel))
            variables
        }
    }

    private fun Map<String, List<EnumeratedSymbolicType>>.contexts(): List<Map<String, EnumeratedSymbolicType>> {
        val m = LinkedHashMap(this)
        return naryCartesianProduct(m.values.toList()).map { this.keys.zip(it).toMap() }
    }
}
