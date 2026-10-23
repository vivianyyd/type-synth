package bench

import oneast.*
import testutil.ocaml.OCamlGroundTruth

/**
 * A version of the search to benchmark, as a change to each benchmark's default configuration.
 * Variants combine: `--variant sound,auto3` applies both, in order.
 *
 * Add a variant here for each alternative worth keeping side by side, i.e. each row of an
 * ablation. A change that only lives on a branch needs no variant: runs record the commit.
 *
 * [ocamlGroundTruth] is how OCaml benchmarks ask OCaml about examples, or null to leave it alone.
 */
class Variant(
    val name: String,
    val description: String,
    val ocamlGroundTruth: OCamlGroundTruth? = null,
    val configure: (Configuration) -> Configuration,
)

object Variants {
    val all: Map<String, Variant> =
        listOf(
            Variant("default", "Each benchmark's own configuration") { it },
            Variant("single-round", "Solve for every name at once") {
                it.copy(scheduleInfo = SingleRound)
            },
            Variant("auto3", "Solve for 3 names per round") { it.copy(scheduleInfo = Auto(3)) },
            Variant("sound", "Let holes nothing constrains also become arrows or any label") {
                it.copy(expansions = Expansions.Sound)
            },
            Variant("simple", "Ignore unification: holes become any variable, an arrow, or any label") {
                it.copy(expansions = Expansions.Simple)
            },
            Variant("observational", "Decide type equality by swapping expressions in the examples") {
                it.copy(oracle = OracleKind.Observational)
            },
            Variant("no-extra-arities", "Never give labels more parameters than the solver's bounds") {
                it.copy(extraArities = 0)
            },
            Variant("no-result-dependence", "Don't bound label arities by how results depend on arguments") {
                it.copy(resultDependence = false)
            },
            Variant(
                "ocaml-toplevel",
                "Ask OCaml about examples with ${OCamlGroundTruth.Toplevel.description}",
                OCamlGroundTruth.Toplevel
            ) { it },
        )
            .associateBy { it.name }

    /** `deepen-arities=N`, which is not in [all] since it takes a bound N. */
    const val DEEPEN = "deepen-arities="
    const val DEEPEN_DESCRIPTION = "Try every label arity up to N, without the solver"

    /** `names-per-round=N`, which is not in [all] since it takes a number N. */
    const val PER_ROUND = "names-per-round="
    const val PER_ROUND_DESCRIPTION = "Solve for N names per round"

    /** `size-bound=N`, which is not in [all] since it takes a number N. */
    const val SIZE = "size-bound="
    const val SIZE_DESCRIPTION = "Fill at most N holes per round"

    private fun one(name: String): Variant {
        fun number() = name.substringAfter("=").toIntOrNull() ?: error("$name needs a number after =")
        return when {
            name.startsWith(DEEPEN) ->
                Variant("$DEEPEN${number()}", DEEPEN_DESCRIPTION) { it.copy(labelArities = LabelArities.Deepened(number())) }
            name.startsWith(SIZE) -> Variant("$SIZE${number()}", SIZE_DESCRIPTION) { it.copy(sizeBound = number()) }
            name.startsWith(PER_ROUND) ->
                Variant("$PER_ROUND${number()}", PER_ROUND_DESCRIPTION) { it.copy(scheduleInfo = Auto(number())) }
            else -> all[name] ?: error("No variant named $name. Try --list")
        }
    }

    /** [names] is one variant, or several separated by commas. */
    fun get(names: String): Variant {
        val vs = names.split(",").map { one(it.trim()) }
        return vs.singleOrNull()
            ?: Variant(
                vs.joinToString("+") { it.name },
                vs.joinToString("; ") { it.description },
                vs.mapNotNull { it.ocamlGroundTruth }.lastOrNull()
            ) { c ->
                vs.fold(c) { acc, v -> v.configure(acc) }
            }
    }
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
        "expansions" to expansions.name,
        "labelArities" to
            when (val la = labelArities) {
                LabelArities.Solved -> mapOf("kind" to "solved")
                is LabelArities.Deepened -> mapOf("kind" to "deepened", "bound" to la.bound)
            },
        "extraArities" to extraArities,
        "resultDependence" to resultDependence,
        "oracle" to oracle.name,
    )
