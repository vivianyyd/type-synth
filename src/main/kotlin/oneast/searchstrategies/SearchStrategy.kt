package oneast.searchstrategies

import oneast.OneUnification
import oneast.SearchState
import oneast.THole
import oneast.Type
import query.Examples

abstract class SearchStrategy(private val examples: Examples) {
    abstract fun candidates(c: SearchState): Sequence<SearchState>

    protected fun posUnification(s: SearchState) = OneUnification(s, examples.posNoSubexprs)

//    protected fun fastForward(candidate: SearchState): Sequence<SearchState> {
//        var curr = candidate
//        do {
//            var changed = false
//            val u = posUnification(curr)
//            curr =
//                curr.mapTypes { t ->
//                    val changes =
//                        t.allHolesWithDepth(topLevel = true).map { (hole, depth) ->
//                            hole to hole.fastForward(u, topLevel = depth == 0)
//                        }
//                    if (changes.isNotEmpty() && changes.any { it.second != null }) changed = true
//                    changes.fold(t) { acc: Type, (hole, ty): Pair<THole, Type?> ->
//                        if (ty == null) acc else acc.replace(hole, ty)
//                    }
//                }
//        } while (changed)
//        return if (curr.noHoles()) sequenceOf(curr) else emptySequence()
//    }

    fun conservativeFastForward(candidate: SearchState): SearchState {
        // TODO Not sure if we need to iterate until fixpoint here
        return fixpoint(candidate, THole::conservativeFastForward)
    }

    fun fastForward(candidate: SearchState): SearchState? {
        val fix = fixpoint(candidate, THole::fastForward)
        return if (fix.noHoles()) fix else null
    }

    private fun fixpoint(
        candidate: SearchState,
        transform: (THole, OneUnification) -> Type?
    ): SearchState {
        var curr = candidate
        do {
            var changed = false
            val u = posUnification(curr)
            curr =
                curr.mapTypes { t ->
                    val changes = t.allHoles().map { it to transform(it, u) }
                    if (changes.isNotEmpty() && changes.any { it.second != null }) changed =
                        true
                    changes.fold(t) { acc: Type, (hole, ty): Pair<THole, Type?> ->
                        if (ty == null) acc else acc.replace(hole, ty)
                    }
                }
        } while (changed)
        return curr
    }
}
