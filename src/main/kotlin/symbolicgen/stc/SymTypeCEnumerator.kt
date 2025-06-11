package symbolicgen.stc

import query.App
import query.Example
import query.Name
import query.Query
import symbolicgen.sta.*
import symbolicgen.sta.Function
import util.EqualityNewOracle
import util.UnionFind
import util.naryCartesianProduct

class SymTypeCEnumerator(
    val query: Query,
    state: State,
    private val oracle: EqualityNewOracle,
) {
    private val state = state.read()

    var freshLabel = 0

    val varTypeIds = query.names.withIndex().associate { (i, n) -> n to i }
    private fun tId(name: String) = varTypeIds[name]!!

    fun enumerateAll(): List<Map<String, SymTypeC>> {
        val all = state.mapValues { (n, options) ->
            options.flatMap { enumerate(it, 0, false, n, false).map { it.first } }
        }.contexts().map { it.toMutableMap() }
        return all.filter(::checkPosExsAndMergeLabels)
    }

    /**
     * checks positive examples, and introduces label equivalences as needed
     */
    private fun checkPosExsAndMergeLabels(context: MutableMap<String, SymTypeC>): Boolean {
        val labelClasses = UnionFind(freshLabel)

        // TODO so hacky. There must be a more principled way...
        context.toList().forEachIndexed { i, (n1, t1) ->
            context.toList().forEachIndexed { j, (n2, t2) ->
                if (i < j && t1 is L && t2 is L && oracle.equal(Name(n1), Name(n2)))
                    labelClasses.union(t1.label, t2.label)
            }
        }

        fun check(ex: Example): SymTypeC? = when (ex) {
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
        fun updateLs(t: SymTypeC): SymTypeC = when (t) {
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
        t: SymTypeA, vars: Int, pickedLabel: Boolean, name: String, canBeFresh: Boolean
    ): List<Triple<SymTypeC, Int, Boolean>> = when (t) {
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
            val variables: MutableList<Triple<SymTypeC, Int, Boolean>> =
                (0 until vars).map { Triple(VR(it, tId(name)), vars, pickedLabel) }.toMutableList()
            if (canBeFresh) variables.add(Triple(VB(vars, tId(name)), vars + 1, pickedLabel))
            // VLs can only appear in the rightmost position. VBs can actually have been previously bound in a label
            else if (pickedLabel) variables.add(Triple(VL(vars, tId(name)), vars + 1, pickedLabel))
            variables
        }
    }

    private fun Map<String, List<SymTypeC>>.contexts(): List<Map<String, SymTypeC>> {
        val m = LinkedHashMap(this)
        return naryCartesianProduct(m.values.toList()).map { this.keys.zip(it).toMap() }
    }
}
