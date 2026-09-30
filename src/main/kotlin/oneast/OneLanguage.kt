package oneast

import java.lang.Integer.max

class SearchState(
    /** maps component names to the index of their type in [types]. */
    val names: Map<String, Int>,
    /**
     * contains enumerated types such that all types enumerated in round i appear before all types
     * enumerated in round j > i.
     */
    val types: List<Type>,
    val labelArities: Map<Int, Int>,
    /**
     * The first [numCommittedTypes] entries of [types] are committed: their types are immutable
     * across any subsequent search. All mutating helpers below ([mapTypes],
     * [mapTypesAndSetLabelArities], [mapTypeAtIndex]) only apply transforms to indices
     * `>= numCommittedTypes`.
     */
    val numCommittedTypes: Int = 0,
    /**
     * The subset of [labelArities] keys whose arities are immutable across any subsequent search.
     * Constraint solvers and rewrites that adjust label arities must pin these labels.
     */
    val committedLabels: Set<Int> = emptySet()
) {
    init {
        require(numCommittedTypes >= 0 && numCommittedTypes <= types.size) {
            "numCommittedTypes is $numCommittedTypes but only ${types.size} types]"
        }
        require(committedLabels.all { it in labelArities }) {
            "Committed labels missing from labelArities: ${committedLabels - labelArities.keys}"
        }
    }

    companion object {
        var nextId = 0

        val emptyState = SearchState(mapOf(), listOf(), mapOf())
    }

    override fun equals(other: Any?): Boolean =
        other is SearchState &&
                other.names == names &&
                other.types == types &&
                other.labelArities == labelArities

    override fun hashCode(): Int {
        var result = names.hashCode()
        result = 31 * result + types.hashCode()
        result = 31 * result + labelArities.hashCode()
        return result
    }

    val id = nextId++

    /**
     * Returns a copy of this state with every current name and label marked as committed. Used to
     * promote a previously-found solution to a fixed seed for a later search.
     */
    fun commitAll(): SearchState =
        SearchState(
            names = names,
            types = types,
            labelArities = labelArities,
            numCommittedTypes = types.size,
            committedLabels = labelArities.keys.toSet()
        )

    fun fnArities(): Map<String, Int> = names.mapValues { (_, i) -> types[i].fnArity() }

    /** @return (index of type containing shallowest fillable hole, the hole, depth of the hole). */
    fun shallowestFillableHole(): Triple<Int, TypeHole, Int>? =
        types
            .withIndex()
            .mapNotNull { ti ->
                ti.value.shallowestFillableHole(topLevel = true)?.let { ti.index to it }
            }
            .minByOrNull { it.second.second }
            ?.let { Triple(it.first, it.second.first, it.second.second) }

    fun noFillableHoles() = types.all { it.shallowestFillableHole(topLevel = true) == null }

    fun numFillableHoles() = types.sumOf { it.numFillableHoles() }

    fun noHoles() = types.all { it.noHoles() }

    fun typeOf(name: String): Type {
        if (name !in names) error("$name not in $names")
        return types[names[name]!!]
    }

    fun maxParamDepth() = types.maxOf { it.maxParamDepth(countArrow = false) }

    private val asMap by lazy { names.mapValues { (_, i) -> types[i] } }

    fun asMap() = asMap

    private fun <T> safeMapTypes(transform: (Type) -> T): List<T> {
        val mappedTypes = types.map(transform)
        require(mappedTypes.withIndex().all { (i, t) -> (i >= numCommittedTypes) || (t is Type && t == types[i]) })
        return mappedTypes
    }

    fun mapTypesAndSetLabelArities(newArities: Map<Int, Int>, transform: (Type) -> Type): SearchState {
        require(newArities.all { (l, a) -> l !in committedLabels || a == labelArities[l]!! })
        return SearchState(
            names = names,
            types = safeMapTypes(transform),
            labelArities = newArities,
            numCommittedTypes = numCommittedTypes,
            committedLabels = committedLabels
        )
    }

    fun mapTypes(transform: (Type) -> Type): SearchState =
        SearchState(
            names = names,
            types = safeMapTypes(transform),
            labelArities = labelArities,
            numCommittedTypes = numCommittedTypes,
            committedLabels = committedLabels
        )

    fun mapTypeAtIndex(i: Int, transform: (Type) -> Type): SearchState {
        require(i >= numCommittedTypes) { "Cannot modify committed type at index $i" }
        return SearchState(
            names = names,
            types = types.mapIndexed { j, t -> if (i == j) transform(t) else t },
            labelArities = labelArities,
            numCommittedTypes = numCommittedTypes,
            committedLabels = committedLabels
        )
    }

    override fun toString() = asMap.toString()
}

sealed interface Type {
    fun maxParamDepth(countArrow: Boolean): Int

    fun noHoles(): Boolean = allHoles().isEmpty()

    fun allHoles(): List<THole>

    fun numFillableHoles() = allHoles().filterIsInstance<TypeHole>().size

    fun blanks() = allHoles().filterIsInstance<Blank>()

    fun shallowestFillableHole(topLevel: Boolean): Pair<TypeHole, Int>?

    fun variables(): Set<Int>

    fun replace(hole: THole, replacement: Type): Type

    /** The number of parameters this type has. */
    fun fnArity(): Int =
        when (this) {
            is Arrow -> 1 + r.fnArity()
            else -> 1
        }
}

sealed class Constructor(open val params: List<Type>) : Type {
    override fun allHoles() = params.flatMap { it.allHoles() }

    override fun variables() = params.flatMap { it.variables() }.toSet()
}

data class Variable(val v: Int) : Type {
    override fun maxParamDepth(countArrow: Boolean) = 0

    override fun allHoles() = emptyList<THole>()

    override fun shallowestFillableHole(topLevel: Boolean) = null

    override fun variables() = setOf(this.v)

    override fun replace(hole: THole, replacement: Type) = this

    override fun toString() = "V$v"
}

data class Arrow(val l: Type, val r: Type) : Constructor(listOf(l, r)) {
    private fun lastParam(): Type {
        fun lastParam(t: Type): Type =
            when (t) {
                is Arrow -> lastParam(t.r)
                is NamedLabel,
                is THole,
                is Variable -> t
            }
        return lastParam(this)
    }

    override fun shallowestFillableHole(topLevel: Boolean): Pair<TypeHole, Int>? {
        val left = l.shallowestFillableHole(topLevel = false)
        val rite = r.shallowestFillableHole(topLevel = topLevel)
        val riteAdjusted =
            // This physical equality check works since holes are not data classes
            if (topLevel && rite != null && rite.first == lastParam()) rite.first to -1 else rite
        return listOfNotNull(left, riteAdjusted)
            .minByOrNull { it.second }
            ?.let { it.first to it.second + (if (topLevel) 0 else 1) }
    }

    override fun maxParamDepth(countArrow: Boolean) =
        (if (countArrow) 1 else 0) + max(l.maxParamDepth(true), r.maxParamDepth(countArrow))

    override fun replace(hole: THole, replacement: Type) =
        Arrow(l.replace(hole, replacement), r.replace(hole, replacement))

    override fun toString() = "${if (l is Arrow) "($l)" else "$l"} -> $r"
}

/** Could also be called DefinedLabel? */
data class NamedLabel(val label: Int, override val params: List<Type>) : Constructor(params) {
    override fun shallowestFillableHole(topLevel: Boolean) =
        params
            .mapNotNull { it.shallowestFillableHole(topLevel) }
            .minByOrNull { it.second }
            ?.let { it.first to it.second + 1 }

    override fun maxParamDepth(countArrow: Boolean) =
        // 1 plus the max depth of any child, or 0 if this node is a leaf
        params.maxOfOrNull { it.maxParamDepth(countArrow) }?.let { it + 1 } ?: 0

    override fun replace(hole: THole, replacement: Type) =
        copy(params = params.map { it.replace(hole, replacement) })

    override fun toString() = "L$label[${params.joinToString(", ")}]"
}

sealed class THole : Type {
    companion object {
        var nextId = 0
    }

    val id = nextId++

    override fun maxParamDepth(countArrow: Boolean) = 0

    override fun allHoles() = listOf(this)

    override fun variables() = emptySet<Int>()

    override fun replace(hole: THole, replacement: Type) = if (hole == this) replacement else this

    /** [sound]: see [Configuration.soundExpansions]. */
    abstract fun expansions(
        unification: OneUnification,
        labelArities: Map<Int, Int>,
        vars: Int,
        canBeVar: Boolean,
        emitLabelBlanks: Boolean,
        emitConstructors: Boolean,
        mustBeLeaf: Boolean,
        sound: Boolean
    ): List<Type>
}

class TypeHole : THole() {
    override fun shallowestFillableHole(topLevel: Boolean) = this to 0

    override fun expansions(
        unification: OneUnification,
        labelArities: Map<Int, Int>,
        vars: Int,
        canBeVar: Boolean,
        emitLabelBlanks: Boolean,
        emitConstructors: Boolean,
        mustBeLeaf: Boolean,
        sound: Boolean
    ): List<Type> =
        if (mustBeLeaf)
            expansionsNoBound(
                unification, labelArities, vars, canBeVar, emitLabelBlanks, emitConstructors, sound
            )
                .filter {
                    when (it) {
                        is Variable -> true
                        is NamedLabel -> it.params.isEmpty()
                        is Arrow -> false
                        is Blank -> true
                        is TypeHole -> throw Exception("Expansions cannot include type holes")
                    }
                }
        else
            expansionsNoBound(
                unification, labelArities, vars, canBeVar, emitLabelBlanks, emitConstructors, sound
            )

    private fun expansionsNoBound(
        unification: OneUnification,
        labelArities: Map<Int, Int>,
        vars: Int,
        canBeVar: Boolean,
        emitLabelBlanks: Boolean,
        emitConstructors: Boolean,
        sound: Boolean
    ): List<Type> {
        val variableExps = if (canBeVar) (0 until vars + 1).map { Variable(it) } else emptyList()
        val fnExpansion = Arrow(TypeHole(), TypeHole())
        val labelExpansions = labelArities.map { NamedLabel(it.key, List(it.value) { TypeHole() }) }

        val constructors =
            if (!emitConstructors) null
            else when (val constructor = unification.holeConstructor(this)) {
                HoleConstructor.None ->
                    if (sound) {
                        if (emitLabelBlanks) listOf(Blank(labelOnly = true), fnExpansion)
                        else labelExpansions + fnExpansion
                    } else {
                        if (emitLabelBlanks) listOf(Blank(labelOnly = true)) else null
                    }
                HoleConstructor.Conflicting -> null
                HoleConstructor.Arrow -> listOf(fnExpansion)
                is HoleConstructor.Label -> labelExpansions.filter { it.label == constructor.label }
            }
        return constructors.orEmpty() + variableExps
    }

    override fun toString() = "_"
}

/**
 * [labelOnly] denotes whether this Blank may be any type or only labels. It's an
 * optimization; it is equivalent to fast forward to all types, but that will produce duplicates.
 */
class Blank(val labelOnly: Boolean) : THole() {
    override fun shallowestFillableHole(topLevel: Boolean) = null

    override fun expansions(
        unification: OneUnification,
        labelArities: Map<Int, Int>,
        vars: Int,
        canBeVar: Boolean,
        emitLabelBlanks: Boolean,
        emitConstructors: Boolean,
        mustBeLeaf: Boolean,
        sound: Boolean
    ) = listOf(this)

    override fun toString() = if (labelOnly) ".L" else "."
}
