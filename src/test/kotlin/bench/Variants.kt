package bench

import oneast.*

/**
 * A version of the search to benchmark, as a change to each benchmark's default configuration.
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
        )
            .associateBy { it.name }

    fun get(name: String) = all[name] ?: error("No variant named $name. Try --list")
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
    )
