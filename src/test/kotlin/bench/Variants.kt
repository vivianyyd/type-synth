package bench

import oneast.*

/**
 * A version of the search to benchmark, as a change to each benchmark's default configuration,
 * which may depend on the problem. Variants combine: `--variant sound,auto3` applies both, in order.
 *
 * Add a variant here for each alternative worth keeping side by side, i.e. each row of an
 * ablation. A change that only lives on a branch needs no variant: runs record the commit.
 */
class Variant(
    val name: String,
    val description: String,
    val configure: (Configuration, Problem) -> Configuration
)

/** A variant that takes a number N, named [prefix]N. */
class NumberedVariant(val prefix: String, val description: String, val make: (Int) -> Variant)

object Variants {
    val all: Map<String, Variant> =
        listOf(
            Variant("default", "Each benchmark's own configuration") { c, _ -> c },
            Variant("single-round", "Solve for every name at once") { c, _ ->
                c.copy(scheduleInfo = SingleRound)
            },
            Variant("auto3", "Solve for 3 names per round") { c, _ -> c.copy(scheduleInfo = Auto(3)) },
            Variant("sound", "Let holes nothing constrains also become arrows or any label") { c, _ ->
                c.copy(soundExpansions = true)
            },
        )
            .associateBy { it.name }

    val numbered: List<NumberedVariant> =
        listOf(
            NumberedVariant("deepen-arities=", "Try every label arity up to N, without the solver") { n ->
                Variant("deepen-arities=$n", "Try every label arity up to $n, without the solver") { c, _ ->
                    c.copy(labelArities = LabelArities.Deepened(n))
                }
            },
            NumberedVariant(
                "given-labels=",
                "Concretize with the expected answer's labels and N more of each arity up to its " +
                    "largest, without outlining"
            ) { n ->
                Variant("given-labels=$n", "Expected answer's labels and $n more of each arity") { c, p ->
                    c.copy(givenLabels = givenLabels(p, n))
                }
            },
        )

    private fun one(name: String): Variant {
        all[name]?.let { return it }
        val v = numbered.firstOrNull { name.startsWith(it.prefix) } ?: error("No variant named $name. Try --list")
        return v.make(name.removePrefix(v.prefix).toIntOrNull() ?: error("$name needs a number after ="))
    }

    /** [names] is one variant, or several separated by commas. */
    fun get(names: String): Variant {
        val vs = names.split(",").map { one(it.trim()) }
        return vs.singleOrNull()
            ?: Variant(vs.joinToString("+") { it.name }, vs.joinToString("; ") { it.description }) { c, p ->
                vs.fold(c) { acc, v -> v.configure(acc, p) }
            }
    }
}

/**
 * The labels in the expected types of the names [p] solves for, and [spare] fresh labels of each
 * arity from 0 to the largest of those.
 */
private fun givenLabels(p: Problem, spare: Int): Map<Int, Int> {
    val expected = p.expected ?: error("given-labels needs a benchmark with an expected answer")
    val needed = p.query.examples.names
        .flatMap { expected.typeOf(it).labels() }
        .toMap()
    val fresh = generateSequence((expected.labelArities.keys.maxOrNull() ?: -1) + 1) { it + 1 }.iterator()
    val spares = (0..(needed.values.maxOrNull() ?: 0)).flatMap { a -> List(spare) { fresh.next() to a } }
    return needed + spares
}

/** The configuration as it is recorded with each run. */
fun Configuration.toJson(): Map<String, Any?> =
    linkedMapOf(
        "searchStrategy" to searchStrategy.name,
        "sizeBound" to sizeBound,
        "depthBound" to depthBound,
        "schedule" to
            when (val s = scheduleInfo) {
                is SingleRound -> mapOf("kind" to "single")
                is Auto -> mapOf("kind" to "auto", "namesPerRound" to s.namesPerRound)
                is CustomSchedule -> mapOf("kind" to "custom", "rounds" to s.customSchedule)
            },
        "numSols" to numSols.toString(),
        "soundExpansions" to soundExpansions,
        "labelArities" to
            when (val la = labelArities) {
                LabelArities.Solved -> mapOf("kind" to "solved")
                is LabelArities.Deepened -> mapOf("kind" to "deepened", "bound" to la.bound)
            },
        "givenLabels" to givenLabels,
    )
