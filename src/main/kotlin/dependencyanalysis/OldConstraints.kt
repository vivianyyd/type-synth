package dependencyanalysis

import stc.Projection
import stc.Var
import util.equivalenceClasses

sealed interface DependencyConstraint

// TODO MustSuperSet/SubSet. Don't really know how to use these anyway so not implemented yet
object ContainsNoVariables : DependencyConstraint

data class ContainsOnly(val vId: Int, val tId: Int) : DependencyConstraint

data class MustContainVariables(val vars: List<Pair<Int, Int>>) : DependencyConstraint

// TODO make it map from ParameterNodes
/**
 * Take a dependency analysis (arrows on an arity hypothesis) and outline (hypothesis of label and
 * variable locations) and produce explicit variable constraints for each parameter in the outline.
 */
fun constraintsForOldPipeline(outline: Projection, deps: ArrowDependencyAnalysis) =
    outline.outline.keys.associateWith { name ->
        val graph = deps.graphs[name]!!
        val constrs = mutableMapOf<Int, DependencyConstraint>()
        graph.loops.forEach { constrs[it.node.i] = ContainsNoVariables }
        graph.deps.forEach {
            val sup = outline.parameterToType[it.sup]!!
            if (sup is Var) constrs[it.sub.i] = ContainsOnly(sup.vId, sup.tId)
        }
        equivalenceClasses(graph.deps) { e1, e2 -> e1.sup == e2.sup }
            .forEach {
                val sink = it.first().sup
                val containedVars =
                    it.map { outline.parameterToType[it.sub]!! }
                        .filterIsInstance<Var>()
                        .map { it.vId to it.tId }
                if (outline.parameterToType[sink]!! !is Var && containedVars.isNotEmpty()) {
                    if (sink.i !in constrs) constrs[sink.i] = MustContainVariables(containedVars)
                }
            }
        constrs
    }
