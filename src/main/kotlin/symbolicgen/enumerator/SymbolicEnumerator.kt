package symbolicgen.enumerator

import symbolicgen.*
import symbolicgen.Function
import symbolicgen.sketcher.*
import util.*

class SymbolicEnumerator(
    val query: NewQuery,
    state: State,
//    private val oracle: EqualityNewOracle,
//    val rounds: Int? = null
) {
    private val state = state.read()

    private val varTypeIds = query.names.withIndex().associate { (i, n) -> n to i }
    private fun tId(name: String) = varTypeIds[name]!!

    fun enumerateAll(): List<Map<String, SketchedType>> {
        val aa =
            state.mapValues { (n, options) -> options.flatMap { enumerate(it, 0, n, false).unzip().first } }.contexts()
        println(aa.minus(aa.filter(::checkPosExamples))) // TODO removeme after debugging
        return aa.filter(::checkPosExamples)
    }

    private fun checkPosExamples(context: Map<String, SketchedType>): Boolean {
        fun check(ex: Example): SketchedType? = when (ex) {
            is Name -> context[ex.name]!!
            is App -> {
                val f = check(ex.fn)
                if (f is VL) VL else if (f !is F) null else check(ex.arg)?.let { apply(f, it) }
            }
        }
        return query.posExamples.all { check(it) != null }
    }

    private fun enumerate(
        t: SymbolicType,
        vars: Int,
        pickedLabel: Boolean,
        name: String,
        canBeFresh: Boolean
    ): List<Triple<SketchedType, Int, Boolean>> =
        when (t) {
            is Function -> {
                val lefts = t.left.flatMap { enumerate(it, vars, pickedLabel, name, true) }
                lefts.flatMap { (left, lvs, lab) ->
                    val rites = t.rite.flatMap { enumerate(it, lvs, lab, name, false) }
                    rites.map { (rite, rvs, lab) -> Triple(F(left, rite), rvs, lab) }
                }
            }
            is Label -> listOf(Triple(L, vars, true))
            is Variable -> {
                (0 until vars).map { Triple(VR(it, tId(name)), vars, pickedLabel) } +
                        (if (canBeFresh) listOf(Triple(VB(vars, tId(name)), vars + 1, pickedLabel)) else listOf()) +
                        (if (pickedLabel) listOf(Triple(VL, vars, pickedLabel)) else listOf())
            }
        }

    private fun Map<String, List<SketchedType>>.contexts(): List<Map<String, SketchedType>> {
        val m = LinkedHashMap(this)
        return naryCartesianProduct(m.values.toList()).map { this.keys.zip(it).toMap() }
    }
}
