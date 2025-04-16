package symbolicgen.symbolicenumerator

import symbolicgen.*
import symbolicgen.Function
import symbolicgen.symbolicsketcher.*
import util.*

class SymbolicEnumerator(
    val query: NewQuery,
    state: State,
    private val oracle: EqualityNewOracle,
//    val rounds: Int? = null
) {
    private val state = state.read()

    val varTypeIds = query.names.withIndex().associate { (i, n) -> n to i }
    private fun tId(name: String) = varTypeIds[name]!!

    fun enumerateAll(): List<Map<String, SpecializedSymbolicType>> {
        val all = state.mapValues { (n, options) ->
            if (options.size == 1 && options[0] is Label) listOf(CL(oracle.dummy(Name(n))))
            else options.flatMap { enumerate(it, 0, false, n, false).map { it.first } }
        }.contexts()
        return all.filter(::checkPosExamples)
    }

    private fun checkPosExamples(context: Map<String, SpecializedSymbolicType>): Boolean {
        fun check(ex: Example): SpecializedSymbolicType? = when (ex) {
            is Name -> context[ex.name]!!
            is App -> {
                when (val f = check(ex.fn)) {
                    is VL -> f  // This is not actually the output type! It's a hack but it works
                    !is F -> null
                    else -> check(ex.arg)?.let { apply(f, it) }
                }
            }
        }

        val ok = query.posExamples.all { check(it) != null }
        return ok
    }

    private fun enumerate(
        t: SymbolicType,
        vars: Int,
        pickedLabel: Boolean,
        name: String,
        canBeFresh: Boolean
    ): List<Triple<SpecializedSymbolicType, Int, Boolean>> =
        when (t) {
            is Hole -> listOf(Variable(), Label()).flatMap { enumerate(it, vars, pickedLabel, name, canBeFresh) }
            is Function -> {
                val lefts = t.left.flatMap { enumerate(it, vars, pickedLabel, name, true) }
                lefts.flatMap { (left, lvs, lab) ->
                    val rites = t.rite.flatMap { enumerate(it, lvs, lab, name, false) }
                    rites.map { (rite, rvs, lab) -> Triple(F(left, rite), rvs, lab) }
                }
            }
            is Label -> listOf(Triple(L, vars, true))
            is Variable -> {
                val variables: MutableList<Triple<SpecializedSymbolicType, Int, Boolean>> =
                    (0 until vars).map { Triple(VR(it, tId(name)), vars, pickedLabel) }.toMutableList()
                if (canBeFresh)
                    variables.add(Triple(VB(vars, tId(name)), vars + 1, pickedLabel))
                else if (pickedLabel)
                    variables.add(Triple(VL(vars, tId(name)), vars + 1, pickedLabel))
                variables
            }
        }

    private fun Map<String, List<SpecializedSymbolicType>>.contexts(): List<Map<String, SpecializedSymbolicType>> {
        val m = LinkedHashMap(this)
        return naryCartesianProduct(m.values.toList()).map { this.keys.zip(it).toMap() }
    }
}
