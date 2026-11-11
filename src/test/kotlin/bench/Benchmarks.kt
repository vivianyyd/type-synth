package bench

import oneast.*
import query.AbstractQuery
import testutil.loadQueryFromFile
import testutil.ocamlName
import testutil.ocaml.OCamlModuleGroup
import testutil.ocaml.ocamlModuleGroup
import testutil.ocaml.ocamlModuleGroups
import testutil.ocaml.ocamlModulesQuery
import testutil.ocaml.withDependencies
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

private fun sexp(file: String, defaults: Configuration = sexpDefaults, name: String = file) =
    oneStep(name, defaults) { _ ->
        val query = loadQueryFromFile(file)
        Problem(query, query.oracle, query.oracle.truth)
    }

/** Solves [group] given the true types of the groups it depends on. */
private fun ocaml(group: OCamlModuleGroup) =
    oneStep("ocaml-${group.name}", ocamlDefaults) { groundTruth ->
        val fixed = withDependencies(group).dropLast(1).flatMap { it.files }
        val (query, expected) = ocamlModulesQuery(group.files, fixed, groundTruth = groundTruth)
        Problem(query, groundTruth, expected)
    }

/**
 * Solves [groups] in order, each given the search's own answer for the groups before it: step i has
 * the examples of every group up to the ith, committed to the answer of the step before it.
 */
private fun ocamlChained(name: String, groups: List<OCamlModuleGroup>) =
    Benchmark(
        name,
        ocamlDefaults,
        groups.mapIndexed { i, group ->
            Step(group.name) { committed, groundTruth ->
                val files = groups.subList(0, i + 1).flatMap { it.files }
                val (query, expected) = ocamlModulesQuery(files, fixed = emptyList(), committed, groundTruth)
                Problem(query, groundTruth, expected)
            }
        }
    )

/** label-merge with a first round of every name but p and q, then [rounds]. */
private fun labelMergeAfterHelpers(name: String, vararg rounds: List<String>) =
    sexp(
        "label-merge",
        sexpDefaults.copy(
            scheduleInfo =
                CustomSchedule(
                    (listOf(listOf("one", "lv", "nv", "inc", "mk", "k", "m", "n")) + rounds.toList())
                        .map { it.map(::ocamlName) }
                )
        ),
        name,
    )

/**
 * p's label is fixed only through k q p, by q's parameter, which m q fixes. An outline gives p a new
 * label of its own, so no search with the solver's label arities finds q a type, and re-solving the
 * rounds as one doesn't help. With one more parameter allowed, M gets two and the answer is wrong.
 */
private val labelMerge =
    listOf(
        sexp("label-merge"),
        labelMergeAfterHelpers("label-merge-pq", listOf("p", "q")),
        labelMergeAfterHelpers("label-merge-p-q", listOf("p"), listOf("q")),
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
                    .map(::sexp) +
                    // In one round, its eight names give too many outlines to search in minutes
                    sexp(
                        "polymorphic-zip",
                        sexpDefaults.copy(
                            scheduleInfo =
                                CustomSchedule(
                                    listOf(listOf("Num", "true", "nil", "cons"), listOf("{}", "put", "chain", "zip"))
                                        .map { it.map(::ocamlName) }
                                )
                        )
                    ),
            "sexp-unsolved" to listOf("list-and-dict", "option", "pair").map(::sexp) + labelMerge,
            "ocaml" to ocamlModuleGroups.map(::ocaml),
        )

    /** The groups that ocaml-GROUP solves in seconds, as one chain. */
    private val fastChain =
        ocamlChained(
            "ocaml-chained-fast",
            listOf(
                "basics", "comparison", "arith", "boolean", "char", "bitwise", "str", "unit", "pair_mod", "pair",
                "float", "bool_mod", "char_mod", "unit_mod", "option_mod", "strconv", "fun_mod",
            )
                .map(::ocamlModuleGroup)
        )

    /**
     * The full chain, the fast one, and for each group, the chain of only it and the groups it
     * depends on.
     */
    private val chains =
        listOf(ocamlChained("ocaml-chained", ocamlModuleGroups), fastChain) +
            ocamlModuleGroups.map { ocamlChained("ocaml-chained-${it.name}", withDependencies(it)) }

    val all: Map<String, Benchmark> = (suites.values.flatten() + chains).associateBy { it.name }

    /** Each of [names] is a benchmark or a suite. */
    fun resolve(names: List<String>): List<Benchmark> =
        names
            .flatMap {
                suites[it] ?: listOf(all[it] ?: error("No benchmark or suite named $it. Try --list"))
            }
            .distinct()
}
