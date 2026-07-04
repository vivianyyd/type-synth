package oneast.searchstrategies

import oneast.OneUnification
import oneast.SearchState
import query.Examples

abstract class SearchStrategy(private val examples: Examples) {
    /**
     * Lazily produces refinements of the seed [c] that pass [examples]. Output states are not
     * guaranteed to be concrete, but they are as concretized as this SearchStrategy will allow
     */
    abstract fun candidates(c: SearchState): Sequence<SearchState>

    protected fun posUnification(s: SearchState) = OneUnification(s, examples.posNoSubexprs)

    protected fun failsNegexWithNoHoleConstraints(s: SearchState) =
        examples.neg.any { OneUnification(s, listOf(it)).passedWithNoConstraints() }.let{
//            if (it) {
//                examples.neg.forEach{
//                    val u = OneUnification(
//                        s,
//                        listOf(it)
//                    )
//                    if (u.passedWithNoConstraints()) {
//                        println("failed on negex $it")
//                        println("\tclasses $u")
//                    }
//                }
//            }
            it
        }

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
//    fun conservativeFastForward(
//        candidate: SearchState,
//        depthBound: Int,
//    ): Sequence<SearchState> {
//        // TODO Not sure if we need to iterate until fixpoint here, I think yes bc we don't follow
//        // inst ptrs but constraints do propagate
//        return fixpoint(candidate, THole::conservativeFastForward, depthBound)?.let {
//            sequenceOf(it)
//        } ?: emptySequence()
//    }

//    private fun fixpoint(
//        candidate: SearchState,
//        transform: (THole, OneUnification) -> Type?,
//        depthBound: Int,
//    ): SearchState? {
//        var curr = candidate
//        var ok: Boolean
//        do {
//            var changed = false
//            val u = posUnification(curr)
//            ok = curr.maxParamDepth() <= depthBound && u.ok // force the thunk, and enforce bound
//            if (!ok) break
//            curr =
//                curr.mapTypes { t ->
//                    val changes = t.allHoles().map { it to transform(it, u) }
//                    if (changes.isNotEmpty() && changes.any { it.second != null }) changed = true
//                    changes.fold(t) { acc: Type, (hole, ty): Pair<THole, Type?> ->
//                        if (ty == null) acc else acc.replace(hole, ty)
//                    }
//                }
//        } while (changed)
//        return if (posUnification(curr).ok) curr else null
//    }

//    fun unionFastForward(candidate: SearchState, depthBound: Int): Sequence<SearchState> =
//        fixpoint(candidate, ::unionFastForward, depthBound)?.let { sequenceOf(it) }
//            ?: emptySequence()
//
//    private fun unionFastForward(candidate: SearchState): SearchState? {
//        val u = posUnification(candidate)
//        if (!u.ok) return null
//        val uf = IntUnionFind()
//
//        candidate.types
//            .flatMap { it.allHoles() }
//            .forEach { hole ->
//                u.boundHoles(hole).forEach { other ->
//                    uf.union(hole.id, other.hole.id)
//                }
//            }
//
//        // TODO think: maybe it's ok to be more aggro/ make something a label even if one of the
//        //   holes it unifies with is a variable... for now let's be more conservative
//
//        val canonicalToConstraints = mutableMapOf<Int, MutableList<ConstraintTy>>()
//        val holes = candidate.types.flatMap { it.allHoles() }
//        holes.forEach {
//            val equals = u.boundConstructors(it)
//            val canonical = uf.find(it.id) ?: it.id
//            canonicalToConstraints.getOrPut(canonical) { mutableListOf() }.addAll(equals)
//        }
//
//        /**
//         * Iterate through types and substitute antiunifiers for holes. We call antiunify() each
//         * time since we must instantiate new holes for each new occurrence of the antiunifier.
//         */
//        fun getAntiunifier(h: THole): Type? {
//            val exprs = canonicalToConstraints[uf.find(h.id) ?: h.id] ?: emptyList()
//            return THole.antiunify(exprs) { TypeHole() }
//        }
//
//        fun replaceTypes(t: Type): Type? =
//            when (t) {
//                is Arrow ->
//                    replaceTypes(t.l)?.let { l -> replaceTypes(t.r)?.let { r -> Arrow(l, r) } }
//                is NamedLabel -> {
//                    val p = t.params.map { replaceTypes(it) }
//                    if (null in p) null else t.copy(params = p.requireNoNulls())
//                }
//                is THole -> {
//                    val au = getAntiunifier(t)
//                    // If we can't fast forward, we should keep the original hole. This is
//                    // important, it is the base case; otherwise we recurse infinitely when solving
//                    // for fixpt.
//                    if (au is THole) t else au
//                }
//                is Variable -> t
//            }
//        return candidate.mapTypesOrNull { replaceTypes(it) }
//    }

//    private fun fixpoint(
//        candidate: SearchState,
//        transform: (SearchState) -> SearchState?,
//        depthBound: Int
//    ): SearchState? {
//        var curr = candidate
//        while (true) {
//            if (curr.maxParamDepth() > depthBound) return null
//            val transformed = transform(curr) ?: return null
//            if (transformed.types == curr.types) break
//            curr = transformed
//        }
//        return if (posUnification(curr).ok) curr else null
//    }
}
