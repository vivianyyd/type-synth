package oneast.searchstrategies

import oneast.OneUnification
import oneast.SearchState
import oneast.THole
import oneast.Type
import query.Examples
import util.Logger

abstract class SearchStrategy(private val examples: Examples) {
    abstract fun candidates(
        c: SearchState,
        unification: OneUnification,
        emitLabelBlanks: Boolean,
        sizeBound: Int,
        depthBound: Int,
        logger: Logger
    ): Sequence<SearchState>

    protected fun posUnification(s: SearchState) = OneUnification(s, examples.posNoSubexprs)

    protected fun fastForward(candidate: SearchState): Sequence<SearchState> {
        var curr = candidate
        do {
            var changed = false
            val u = posUnification(curr)
            curr =
                curr.mapTypes { t ->
                    val changes =
                        t.allHolesWithDepth(topLevel = true).map { (hole, depth) ->
                            hole to hole.fastForward(u, topLevel = depth == 0)
                        }
                    if (changes.isNotEmpty() && changes.any { it.second != null }) changed = true
                    changes.fold(t) { acc: Type, (hole, ty): Pair<THole, Type?> ->
                        if (ty == null) acc else acc.replace(hole, ty)
                    }
                }
        } while (changed)
        return if (curr.noHoles()) sequenceOf(curr) else emptySequence()
    }
}
