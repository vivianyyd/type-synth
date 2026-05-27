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
     * across any subsequent search. All mutating helpers below ([mapTypes], [mapTypesOrNull],
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

    fun blanks() = types.flatMap { it.blanks() }

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

    fun mapTypesOrNull(transform: (Type) -> Type?): SearchState? {
        val newTypes = safeMapTypes(transform)
        return if (null in newTypes) null else
            SearchState(
                names = names,
                types = newTypes.requireNoNulls(),
                labelArities = labelArities,
                numCommittedTypes = numCommittedTypes,
                committedLabels = committedLabels
            )
    }

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
    private fun lastParamVariables(): Set<Int> =
        when (this) {
            is Arrow -> r.lastParamVariables()
            is NamedLabel,
            is THole,
            is Variable -> variables()
        }

    private fun variablesBeforeLastParam(rightPath: Boolean = true): Set<Int> =
        when (this) {
            is Arrow ->
                if (rightPath)
                    l.variablesBeforeLastParam(rightPath = false) /* == variables() */ +
                        r.variablesBeforeLastParam(rightPath = true)
                else variables()
            is NamedLabel,
            is THole,
            is Variable -> if (rightPath) emptySet() else variables()
        }

    /**
     * A valid *top-level* type cannot be concrete and have a fresh variable in the output type. It
     * also can't just be any arbitrary variable. The latter should never happen since we will not
     * enumerate Variables if the hole is a root, so we skip that check here. This is obviously not
     * true for any subterm of a type so idk maybe there should be some extra class somewhere but
     * whatever
     *
     * Correction 4/20/26: Actually, we do want to support having fresh variables in the output, for
     * example for functions on_exit: unit -> 'a and Left: 'a -> Either 'a 'b. As consequence, we no
     * longer call this
     */
    fun invalid() = noHoles() && freshVariableInOutput()

    private fun freshVariableInOutput() =
        when (this) {
            is Arrow -> (lastParamVariables() - variablesBeforeLastParam()).isNotEmpty()
            is NamedLabel,
            is THole,
            is Variable -> false
        }

    fun maxParamDepth(countArrow: Boolean): Int

    fun instantiate(instId: Int): ConstraintTy

    fun noHoles(): Boolean = allHoles().isEmpty()

    fun allHoles(): List<THole>

    fun numFillableHoles() = allHoles().filterIsInstance<TypeHole>().size

    fun blanks() = allHoles().filterIsInstance<Blank>()

    fun allHolesWithDepth(topLevel: Boolean): List<Pair<THole, Int>>

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

    override fun allHolesWithDepth(topLevel: Boolean) = emptyList<Pair<THole, Int>>()

    override fun instantiate(instId: Int): ConstraintTy = ConstraintVariable(v, instId)

    override fun shallowestFillableHole(topLevel: Boolean) = null

    override fun variables() = setOf(this.v)

    override fun replace(hole: THole, replacement: Type) = this

    override fun toString() = "V$v"
}

data class Arrow(val l: Type, val r: Type) : Constructor(listOf(l, r)) {
    override fun allHolesWithDepth(topLevel: Boolean) =
        (l.allHolesWithDepth(topLevel = false) + r.allHolesWithDepth(topLevel = topLevel)).map {
            it.first to it.second + (if (topLevel) 0 else 1)
        }

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

    override fun instantiate(instId: Int): ConstraintTy =
        ConstraintArrow(l.instantiate(instId), r.instantiate(instId))

    override fun replace(hole: THole, replacement: Type) =
        Arrow(l.replace(hole, replacement), r.replace(hole, replacement))

    override fun toString() = "${if (l is Arrow) "($l)" else "$l"} -> $r"
}

/** Could also be called DefinedLabel? */
data class NamedLabel(val label: Int, override val params: List<Type>) : Constructor(params) {
    override fun allHolesWithDepth(topLevel: Boolean) =
        params.flatMap { it.allHolesWithDepth(topLevel).map { it.first to it.second + 1 } }

    override fun shallowestFillableHole(topLevel: Boolean) =
        params
            .mapNotNull { it.shallowestFillableHole(topLevel) }
            .minByOrNull { it.second }
            ?.let { it.first to it.second + 1 }

    override fun maxParamDepth(countArrow: Boolean) =
        // 1 plus the max depth of any child, or 0 if this node is a leaf
        params.maxOfOrNull { it.maxParamDepth(countArrow) }?.let { it + 1 } ?: 0

    override fun instantiate(instId: Int): ConstraintTy =
        ConstraintLabel(label, params.map { it.instantiate(instId) })

    override fun replace(hole: THole, replacement: Type) =
        copy(params = params.map { it.replace(hole, replacement) })

    override fun toString() = "L$label[${params.joinToString(", ")}]"
}

sealed class THole : Type {
    companion object {
        var nextId = 0

        /** So the numbers are smaller for readability. Only call me between phases */
        fun resetIds() {
            nextId = 0
        }

        /**
         * Antiunifies types in [exprs], *ignoring Instantiations and Bottom*. Only considers Variables
         * and Constructors.
         */
        fun antiunify(exprs: List<ConstraintTy>, defaultAntiunifier: () -> Type): Type? {
            if (exprs.isEmpty()) return defaultAntiunifier()
            if (exprs.any { it is ConstraintVariable }) return defaultAntiunifier()

            val constructors = exprs.filterIsInstance<ConstraintTypeConstructor>()

            if (constructors.isEmpty() ||
                constructors.any { a -> constructors.any { b -> !a.match(b) } }
            )
                return defaultAntiunifier()

            // We know they match now
            return when (constructors.first()) {
                is ConstraintArrow -> {
                    antiunify(constructors.map { (it as ConstraintArrow).l }, defaultAntiunifier)
                        ?.let { l ->
                            antiunify(
                                constructors.map { (it as ConstraintArrow).r }, defaultAntiunifier
                            )
                                ?.let { r -> Arrow(l, r) }
                        }
                }
                is ConstraintLabel -> {
                    val params =
                        List(constructors.first().params.size) { i ->
                            antiunify(
                                constructors.map { (it as ConstraintLabel).params[i] },
                                defaultAntiunifier
                            )
                        }
                            .filterNotNull()
                    if (params.size != constructors.first().params.size) null
                    else NamedLabel((constructors.first() as ConstraintLabel).label, params)
                }
            }
        }

    }

    val id = nextId++

    override fun maxParamDepth(countArrow: Boolean) = 0

    override fun allHoles() = listOf(this)

    override fun allHolesWithDepth(topLevel: Boolean) = listOf(this to 0)

    override fun instantiate(instId: Int): ConstraintTy = InstantiationTy(this, instId)

    override fun variables() = emptySet<Int>()

    override fun replace(hole: THole, replacement: Type) = if (hole == this) replacement else this

    abstract fun expansions(
        unification: OneUnification,
        labelArities: Map<Int, Int>,
        vars: Int,
        canBeVar: Boolean,
        emitLabelBlanks: Boolean,
        emitConstructors: Boolean,
        mustBeLeaf: Boolean
    ): List<Type>

    /**
     * A more conservative fast-forward, where we are guaranteed to return a Type iff it was the
     * only way we could continue. We actually want to introduce holes here since we can't guess
     * anything, but we autofill all the holes we can at once. If a hole points to an Instantiation,
     * Variable, or Bottom, we do not fast forward.
     */
    fun conservativeFastForward(unification: OneUnification): Type? {
        val defaultHoleMaker = { TypeHole() }

        val antiunifies = unification.holeEquals(this)
        val constrs = antiunifies.filterIsInstance<ConstraintTypeConstructor>()

        /* It may seem redundant to perform these checks when antiunify() does them as well, but it is
        not. This prevents us from an infinite loop when we try to get the fixpoint of this
        function, since our default antiunification behavior is to make another hole. If at the
        top-level we can't do anything, we shouldn't replace this hole with another hole, we
        should just return no changes. We still want to keep that behavior in antiunify() though,
        since we need it to fill the leaves when we are fast-forwarding to an entire tree. */
        if (constrs.isEmpty() || antiunifies.any { it !is ConstraintTypeConstructor }) return null
        if (constrs.any { a -> constrs.any { b -> !a.match(b) } }) return null
        return antiunify(antiunifies, defaultAntiunifier = defaultHoleMaker)
    }

    /**
     * Fast forward once we've hit our budget, a last-ditch effort to find a solution if we were
     * quite close.
     */
    fun fastForward(unification: OneUnification): Type? {
        val defaultVariable = Variable(0)

        val antiunifies = unification.holeEquals(this)
        val au = antiunify(antiunifies, defaultAntiunifier = { defaultVariable })
        return if (au is Constructor) {
            val instsPointTo =
                antiunifies.filterIsInstance<InstantiationTy>().mapNotNull {
                    // todo this is not efficient, if you read it you'll see we examine things
                    //  multiple times
                    val instEqs = unification.holeEquals(it.hole)
                    // Ignore the other insts if unconstrained, if it can be a variable, or
                    // constructors mismatch
                    if (instEqs.any { it is ConstraintVariable }) null
                    else takeFirstIfMatch(instEqs.filterIsInstance<ConstraintTypeConstructor>())
                }
            takeFirstIfMatch(listOf(au.instantiate(0) as ConstraintTypeConstructor) + instsPointTo)
                ?.toNode()
        } else au
    }

    /** Returns the first node if top-level constructors all match; null if mismatch or empty. */
    private fun takeFirstIfMatch(
        constrs: List<ConstraintTypeConstructor>
    ): ConstraintTypeConstructor? {
        return if (constrs.isEmpty()) null
        else if (constrs.all { a -> constrs.all { b -> a.match(b) } }) {
            // we only care about the top-level constructor, so it suffices to return an arbitrary
            // element
            constrs.first()
        } else null
    }

    private fun ConstraintTy.toNode(): Type =
        when (this) {
            is ConstraintArrow -> Arrow(this.l.toNode(), this.r.toNode())
            is ConstraintLabel -> NamedLabel(this.label, this.params.map { it.toNode() })
            is ConstraintVariable -> Variable(this.v)
            is InstantiationTy -> error("Unreachable pattern match - convert Instantiation to node")
            Bottom -> error("Antiunifying should never produce Bottom")
        }
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
        mustBeLeaf: Boolean
    ): List<Type> =
        if (mustBeLeaf)
            expansionsNoBound(
                unification, labelArities, vars, canBeVar, emitLabelBlanks, emitConstructors
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
                unification, labelArities, vars, canBeVar, emitLabelBlanks, emitConstructors
            )

    private fun expansionsNoBound(
        unification: OneUnification,
        labelArities: Map<Int, Int>,
        vars: Int,
        canBeVar: Boolean,
        emitLabelBlanks: Boolean,
        emitConstructors: Boolean
    ): List<Type> {
        val variableExps = if (canBeVar) (0 until vars + 1).map { Variable(it) } else emptyList()
        val fnExpansion = Arrow(TypeHole(), TypeHole())
        val labelExpansions = labelArities.map { NamedLabel(it.key, List(it.value) { TypeHole() }) }
        // If there are no existing labels, we need to learn them.
        // For now, instead we will explicitly introduce only blanks for expansions
        // An alternate implementation might introduce a blank if [labelExpansions] is empty

        val instances = unification.holeEquals(this).filterIsInstance<ConstraintTypeConstructor>()
        val constructorTypes = // this would be cleaner if implemented as a filter
            if (emitConstructors && instances.isNotEmpty()) {
                val i = instances.first()
                if (instances.any { !i.match(it) }) emptyList()
                else
                    when (i) {
                        is ConstraintArrow -> listOf(fnExpansion)
                        is ConstraintLabel ->
                            if (emitLabelBlanks) emptyList()
                            else labelExpansions.filter { it.label == i.label }
                    }
            } else listOf()
        //                labelExpansions +
        //                        listOf(
        //                            TODO(
        //                                "It's only fast if I make the else branch return no
        // constructors instead of any label. Why was Concrete version so much faster even when
        // adding all label expansions"
        //                            )
        //                        )
        return constructorTypes.ifEmpty { listOfNotNull(Blank(labelOnly = true).takeIf { emitLabelBlanks }) } +
                variableExps
    }

    override fun toString() = "_"
}

/**
 * [labelOnly] denotes whether this Blank may fast forward to any type or only labels. It's an
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
        mustBeLeaf: Boolean
    ) = listOf(this)

    override fun toString() = if (labelOnly) ".L" else "."
}

sealed interface ConstraintTy {
    fun variables(): List<ConstraintVariable>
}

object Bottom : ConstraintTy {
    override fun variables() = emptyList<ConstraintVariable>()

    override fun toString(): String = "⊥"
}

// TODO Consider whether I want two different types of instantiations for TypeHoles vs
//   UnnamedLabels. UnnamedLabels behave differently from TypeHoles because while their
//   instantiated types can differ, they always have the same root. Does it matter?
data class InstantiationTy(val hole: THole, val instId: Int) : ConstraintTy {
    override fun variables() = emptyList<ConstraintVariable>()

    override fun toString(): String = "_${hole.id}-$instId"
}

data class ConstraintVariable(val v: Int, val instId: Int) : ConstraintTy {
    private val variables by lazy { listOf(this) }

    override fun variables() = variables

    override fun toString(): String = "V$v-$instId"
}

sealed class ConstraintTypeConstructor(open val params: List<ConstraintTy>) : ConstraintTy {
    /** Whether this node shallow matches with [other]. */
    abstract fun match(other: ConstraintTypeConstructor): Boolean

    private val variables by lazy { params.flatMap { it.variables() } }

    override fun variables(): List<ConstraintVariable> = variables
}

data class ConstraintArrow(override val params: List<ConstraintTy>) :
    ConstraintTypeConstructor(params) {
    init {
        require(params.size == 2)
    }

    val l = params[0]
    val r = params[1]

    constructor(l: ConstraintTy, r: ConstraintTy) : this(listOf(l, r))

    override fun match(other: ConstraintTypeConstructor) = other is ConstraintArrow

    override fun toString(): String = "($l) -> ($r)"
}

data class ConstraintLabel(val label: Int, override val params: List<ConstraintTy>) :
    ConstraintTypeConstructor(params) {
    override fun match(other: ConstraintTypeConstructor) =
        other is ConstraintLabel && label == other.label && params.size == other.params.size

    override fun toString(): String = "L$label$params"
}
