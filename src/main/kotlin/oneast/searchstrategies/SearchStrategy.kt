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
    //                    if (changes.isNotEmpty() && changes.any { it.second != null }) changed =
    // true
    //                    changes.fold(t) { acc: Type, (hole, ty): Pair<THole, Type?> ->
    //                        if (ty == null) acc else acc.replace(hole, ty)
    //                    }
    //                }
    //        } while (changed)
    //        return if (curr.noHoles()) sequenceOf(curr) else emptySequence()
    //    }

    /** May return an empty sequence, since fast forwarding may uncover a contradiction. */
    fun conservativeFastForward(
        candidate: SearchState,
        depthBound: Int,
    ): Sequence<SearchState> {
        // TODO Not sure if we need to iterate until fixpoint here, I think yes bc we don't follow
        // inst ptrs but constraints do propagate
        return fixpoint(candidate, THole::conservativeFastForward, depthBound)?.let {
            sequenceOf(it)
        } ?: emptySequence()
    }

    fun fastForward(
        candidate: SearchState,
        depthBound: Int,
    ): Sequence<SearchState> {
        val fix = fixpoint(candidate, THole::fastForward, depthBound) ?: return emptySequence()
        return if (fix.noHoles()) sequenceOf(fix) else emptySequence()
    }

    private fun fixpoint(
        candidate: SearchState,
        transform: (THole, OneUnification) -> Type?,
        depthBound: Int,
    ): SearchState? {
        var curr = candidate
        var ok: Boolean
        do {
            var changed = false
            val u = posUnification(curr)
            ok = curr.maxParamDepth() <= depthBound && u.ok // force the thunk, and enforce bound
            if (!ok) break
            curr =
                curr.mapTypes { t ->
                    val changes = t.allHoles().map { it to transform(it, u) }
                    if (changes.isNotEmpty() && changes.any { it.second != null }) changed = true
                    changes.fold(t) { acc: Type, (hole, ty): Pair<THole, Type?> ->
                        if (ty == null) acc else acc.replace(hole, ty)
                    }
                }
        } while (changed)
        return if (ok) curr else null
    }
}
