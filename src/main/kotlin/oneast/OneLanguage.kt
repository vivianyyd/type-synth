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
    /** maps round # (index) to the first index of types enumerated in that round. */
    val rounds: List<Int>,
    val labelArities: Map<Int, Int>
    //    val names: List<String>,
    //    val types: List<Type>
) {
    companion object {
        var nextId = 0

        /** So the numbers are smaller for readability. Only call me between phases */
        fun resetIds() {
            nextId = 0
        }

        val emptyState = SearchState(mapOf(), listOf(), listOf(), mapOf())
    }

    val id = nextId++

    fun fnArities(): Map<String, Int> = names.mapValues { (_, i) -> types[i].fnArity() }

    fun noFillableHoles() = types.all { it.shallowestFillableHole(topLevel = true) == null }

    fun blanks() = types.flatMap { it.blanks() }

    fun noHoles() = types.all { it.noHoles() }

    fun typeOf(name: String) = types[names[name]!!]

    fun maxParamHeight() = types.maxOf { it.maxParamHeight(countArrow = false) }

    private val asMap by lazy { names.mapValues { (_, i) -> types[i] } }

    fun asMap() = asMap

    fun mapTypesAndSetLabelArities(newArities: Map<Int, Int>, transform: (Type) -> Type) =
        SearchState(
            names = names, types = types.map(transform), rounds = rounds, labelArities = newArities
        )

    fun mapTypes(transform: (Type) -> Type): SearchState =
        SearchState(
            names = names,
            types = types.map(transform),
            rounds = rounds,
            labelArities = labelArities
        )

    fun mapTypesIndexed(transform: (Int, Type) -> Type): SearchState =
        SearchState(
            names = names,
            types = types.mapIndexed(transform),
            rounds = rounds,
            labelArities = labelArities
        )

    override fun toString() = asMap.toString()
}

sealed interface Type {
    fun maxParamHeight(countArrow: Boolean): Int

    fun instantiate(instId: Int): ConstraintTy

    fun noHoles(): Boolean = allHoles().isEmpty()

    fun allHoles(): List<THole>

    fun blanks() = allHoles().filterIsInstance<Blank>()

    fun allHolesWithDepth(topLevel: Boolean): List<Pair<THole, Int>>

    fun shallowestFillableHole(topLevel: Boolean): Pair<THole, Int>?

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
    override fun maxParamHeight(countArrow: Boolean) = 1

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

    override fun shallowestFillableHole(topLevel: Boolean) =
        params
            .mapIndexedNotNull { i, p ->
                p.shallowestFillableHole(topLevel = if (i == 0) false else topLevel)
            }
            .minByOrNull { it.second }
            ?.let { it.first to it.second + (if (topLevel) 0 else 1) }

    override fun maxParamHeight(countArrow: Boolean) =
        (if (countArrow) 1 else 0) + max(l.maxParamHeight(true), r.maxParamHeight(countArrow))

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

    override fun maxParamHeight(countArrow: Boolean) =
        1 + (params.maxOfOrNull { it.maxParamHeight(countArrow) } ?: 0)

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
    }

    val id = nextId++

    override fun maxParamHeight(countArrow: Boolean) = 1

    override fun allHoles() = listOf(this)

    override fun allHolesWithDepth(topLevel: Boolean) = listOf(this to 0)

    override fun instantiate(instId: Int): ConstraintTy = InstantiationTy(this, instId)

    override fun variables() = emptySet<Int>()

    override fun replace(hole: THole, replacement: Type) = if (hole == this) replacement else this

    abstract fun expansions(
        unification: OneUnification,
        labelArities: Map<Int, Int>,
        vars: Int,
        topLevel: Boolean,
        introduceBlanks: Boolean,
        mustBeLeaf: Boolean
    ): List<Type>

    fun fastForward(unification: OneUnification, topLevel: Boolean): Type? {
        val defaultVariable =
            if (topLevel) null
            else ConstraintVariable(0, instId = 0) // instId shouldn't matter, dummy here

        val antiunifies = unification.holeEquals(this)
        return antiunify(antiunifies, unification, defaultVariable)?.toNode()
    }

    private fun antiunify(
        exprs: List<ConstraintTy>,
        unification: OneUnification,
        defaultVariable: ConstraintVariable?
    ): ConstraintTy? {
        if (exprs.isEmpty()) return defaultVariable // might as well give this a try
        if (exprs.any { it is ConstraintVariable }) return defaultVariable

        val insts = exprs.filterIsInstance<InstantiationTy>()
        val constructors = exprs.filterIsInstance<ConstraintTypeConstructor>()

        if (constructors.isEmpty() ||
            constructors.any { a -> constructors.any { b -> !a.match(b) } }
        )
            return defaultVariable

        // We know they match now
        val auConstrs =
            when (constructors.first()) {
                is ConstraintArrow -> {
                    antiunify(
                        constructors.map { (it as ConstraintArrow).l },
                        unification,
                        defaultVariable
                    )
                        ?.let { l ->
                            antiunify(
                                constructors.map { (it as ConstraintArrow).r },
                                unification,
                                defaultVariable
                            )
                                ?.let { r -> ConstraintArrow(l, r) }
                        }
                }
                is ConstraintLabel -> {
                    val params =
                        List(constructors.first().params.size) { i ->
                            antiunify(
                                constructors.map { (it as ConstraintLabel).params[i] },
                                unification,
                                defaultVariable
                            )
                        }
                            .filterNotNull()
                    if (params.size != constructors.first().params.size) null
                    else ConstraintLabel((constructors.first() as ConstraintLabel).label, params)
                }
            }

        return if (auConstrs != null) {
            val instsPointTo =
                insts.mapNotNull {
                    // todo this is not efficient, if you read it you'll see we examine things
                    //  multiple times
                    val instEqs = unification.holeEquals(it.hole)
                    // Ignore the other insts if unconstrained, if it can be a variable, or
                    // constructors mismatch
                    if (instEqs.any { it is ConstraintVariable }) null
                    else takeFirstIfMatch(instEqs.filterIsInstance<ConstraintTypeConstructor>())
                }
            takeFirstIfMatch(listOf(auConstrs) + instsPointTo)
        } else null
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
        topLevel: Boolean,
        introduceBlanks: Boolean,
        mustBeLeaf: Boolean
    ): List<Type> =
        if (mustBeLeaf)
            expansionsNoBound(unification, labelArities, vars, topLevel, introduceBlanks).filter {
                when (it) {
                    is Variable -> true
                    is NamedLabel -> it.params.isEmpty()
                    is Arrow -> false
                    is Blank -> true
                    is TypeHole -> throw Exception("Expansions cannot include type holes")
                }
            }
        else expansionsNoBound(unification, labelArities, vars, topLevel, introduceBlanks)

    private fun expansionsNoBound(
        unification: OneUnification,
        labelArities: Map<Int, Int>,
        vars: Int,
        topLevel: Boolean,
        introduceBlanks: Boolean
    ): List<Type> {
        val variableExps = if (topLevel) listOf() else (0 until vars + 1).map { Variable(it) }
        val fnExpansion = Arrow(TypeHole(), TypeHole())
        val labelExpansions = labelArities.map { NamedLabel(it.key, List(it.value) { TypeHole() }) }
        // If there are no existing labels, we need to learn them.
        // For now, instead we will explicitly introduce only blanks for expansions
        // An alternate implementation might introduce a blank if [labelExpansions] is empty

        val instances = unification.holeEquals(this).filterIsInstance<ConstraintTypeConstructor>()
        val constructorTypes = // this would be cleaner if implemented as a filter
            if (instances.isNotEmpty()) {
                val i = instances.first()
                if (instances.any { !i.match(it) }) emptyList()
                else
                    when (i) {
                        is ConstraintArrow -> listOf(fnExpansion)
                        is ConstraintLabel -> labelExpansions.filter { it.label == i.label }
                    }
            } else
                labelExpansions +
                        listOf(
                            TODO(
                                "It's only fast if I make the else branch return no constructors instead of any label. Why was Concrete version so much faster even when adding all label expansions"
                            )
                        )
        return constructorTypes +
                variableExps +
                listOfNotNull(Blank(labelOnly = true).takeIf { introduceBlanks })
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
        topLevel: Boolean,
        introduceBlanks: Boolean,
        mustBeLeaf: Boolean
    ) = listOf(this)

    override fun toString() = if (labelOnly) ".L" else "."
}

sealed interface ConstraintTy {
    fun variables(): List<ConstraintVariable>
}

object Bottom : ConstraintTy {
    override fun variables() = emptyList<ConstraintVariable>()
}

// TODO Consider whether I want two different types of instantiations for TypeHoles vs
//   UnnamedLabels. UnnamedLabels behave differently from TypeHoles because while their
//   instantiated types can differ, they always have the same root. Does it matter?
data class InstantiationTy(val hole: THole, val instId: Int) : ConstraintTy {
    override fun variables() = emptyList<ConstraintVariable>()
}

data class ConstraintVariable(val v: Int, val instId: Int) : ConstraintTy {
    private val variables by lazy { listOf(this) }

    override fun variables() = variables
}

sealed class ConstraintTypeConstructor(open val params: List<ConstraintTy>) : ConstraintTy {
    /** Whether this node shallow matches with [other]. */
    abstract fun match(other: ConstraintTypeConstructor): Boolean

    open fun split(other: ConstraintTypeConstructor) {
        if (match(other)) params.zip(other.params).map { (a, b) -> TODO() } else null
    }

    private val variables by lazy { params.flatMap { it.variables() } }

    override fun variables() = variables
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
}

data class ConstraintLabel(val label: Int, override val params: List<ConstraintTy>) :
    ConstraintTypeConstructor(params) {
    override fun match(other: ConstraintTypeConstructor) =
        other is ConstraintLabel && label == other.label && params.size == other.params.size
}
