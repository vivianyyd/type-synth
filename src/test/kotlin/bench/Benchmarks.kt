package bench

import oneast.*
import query.AbstractQuery
import testutil.loadQueryFromFile
import testutil.ocaml.ocamlModuleGroups
import testutil.ocaml.ocamlModulesQuery
import util.GroundTruth

/** A synthesis problem, and the answer it should have if one is known. */
class Problem(val query: AbstractQuery, val groundTruth: GroundTruth, val expected: SearchState?)

/**
 * One search of a benchmark. [load] builds its problem from the answer the steps before it
 * committed to and the run's ground truth, which a step that checks examples another way ignores.
 */
class Step(val name: String, val load: (committed: SearchState, groundTruth: GroundTruth) -> Problem)

/**
 * Searches solved in order, in one run, each committing to its first solution for the next.
 * [defaults] is the configuration a variant starts from.
 */
class Benchmark(val name: String, val defaults: Configuration, val steps: List<Step>)

/** A benchmark of one step, named like the benchmark. */
private fun oneStep(name: String, defaults: Configuration, load: (groundTruth: GroundTruth) -> Problem) =
    Benchmark(name, defaults, listOf(Step(name) { _, groundTruth -> load(groundTruth) }))

private val sexpDefaults =
    Configuration(
        sizeBound = 20,
        depthBound = 4,
        scheduleInfo = SingleRound,
        numSols = Solutions.NumSolutions(1)
    )

// A round of three list functions, like append, map and fold_left, needs more than 20 holes filled
private val ocamlDefaults = sexpDefaults.copy(scheduleInfo = Auto(3), sizeBound = 30)

private fun sexp(file: String) =
    oneStep(file, sexpDefaults) { _ ->
        val query = loadQueryFromFile(file)
        Problem(query, query.oracle, query.oracle.truth)
    }

private val ocamlModuleNames = listOf("basics", "comparison", "list", "bitwise", "float", "str")

/** Solves the [i]th group of modules given the true types of the groups before it. */
private fun ocaml(name: String, i: Int) =
    oneStep("ocaml-$name", ocamlDefaults) { groundTruth ->
        val (query, expected) =
            ocamlModulesQuery(ocamlModuleGroups[i], fixed = ocamlModuleGroups.subList(0, i).flatten(), groundTruth = groundTruth)
        Problem(query, groundTruth, expected)
    }

/**
 * Solves the groups of modules in order, each given the search's own answer for the groups before
 * it: step i has the examples of every group up to the ith, committed to the answer of the step
 * before it.
 */
private val ocamlChained =
    Benchmark(
        "ocaml-chained",
        ocamlDefaults,
        ocamlModuleNames.mapIndexed { i, name ->
            Step(name) { committed, groundTruth ->
                val (query, expected) =
                    ocamlModulesQuery(ocamlModuleGroups.subList(0, i + 1).flatten(), fixed = emptyList(), committed, groundTruth)
                Problem(query, groundTruth, expected)
            }
        }
    )

object Benchmarks {
    val suites: Map<String, List<Benchmark>> =
        linkedMapOf(
            "sexp" to
                listOf(
                    "cons",
                    "dictchain",
                    "dictput",
                    "hofs",
                    "id-inc",
                    "polymorphic-dictchain",
                    "polymorphic-nil",
                )
                    .map(::sexp),
            "sexp-unsolved" to listOf("list-and-dict", "option", "pair").map(::sexp),
            "ocaml" to ocamlModuleNames.mapIndexed { i, name -> ocaml(name, i) },
        )

    val all: Map<String, Benchmark> = (suites.values.flatten() + ocamlChained).associateBy { it.name }

    /** Each of [names] is a benchmark or a suite. */
    fun resolve(names: List<String>): List<Benchmark> =
        names
            .flatMap {
                suites[it] ?: listOf(all[it] ?: error("No benchmark or suite named $it. Try --list"))
            }
            .distinct()
}
