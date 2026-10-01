package bench

import oneast.*

/**
 * A version of the search to benchmark, as a change to each benchmark's default configuration.
 * Variants combine: `--variant sound,auto3` applies both, in order.
 *
 * Add a variant here for each alternative worth keeping side by side, i.e. each row of an
 * ablation. A change that only lives on a branch needs no variant: runs record the commit.
 */
class Variant(val name: String, val description: String, val configure: (Configuration) -> Configuration)

object Variants {
    val all: Map<String, Variant> =
        listOf(
            Variant("default", "Each benchmark's own configuration") { it },
            Variant("single-round", "Solve for every name at once") {
                it.copy(scheduleInfo = SingleRound)
            },
            Variant("auto3", "Solve for 3 names per round") { it.copy(scheduleInfo = Auto(3)) },
            Variant("sound", "Let holes nothing constrains also become arrows or any label") {
                it.copy(soundExpansions = true)
            },
        )
            .associateBy { it.name }

    /** [names] is one variant, or several separated by commas. */
    fun get(names: String): Variant {
        val vs = names.split(",").map { all[it.trim()] ?: error("No variant named $it. Try --list") }
        return vs.singleOrNull()
            ?: Variant(vs.joinToString("+") { it.name }, vs.joinToString("; ") { it.description }) { c ->
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
        "soundExpansions" to soundExpansions,
    )
