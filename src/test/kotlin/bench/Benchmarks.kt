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

/** [file] with a first round of the helpers, the names that p, q and r's examples use, then [rounds]. */
private fun labelMergeAfterHelpers(name: String, vararg rounds: List<String>, file: String = "label-merge") =
    sexp(
        file,
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
 * label of its own, which clashes with lv's while concretizing q, so the search merges the two
 * labels (see oneast.Search.mergedOutlines). label-merge-3 adds r, tied to q's parameter by k q r
 * the same way, so the parameter is unified with three labels and takes two merges.
 */
private val labelMerge =
    listOf(
        labelMergeAfterHelpers("label-merge-pq", listOf("p", "q")),
        labelMergeAfterHelpers("label-merge-p-q", listOf("p"), listOf("q")),
        labelMergeAfterHelpers("label-merge-3", listOf("p", "q", "r"), file = "label-merge-3"),
    )

/**
 * label-merge in one round. Concretizing fills k's parameter, then m's, then mk's, so when it fills
 * m's, nothing says it is L. It only gets a variable, which accepts m (mk one), so concretizing
 * reaches no clash to merge. With Expansions.Simple it does, and finds the answer. With
 * one more parameter allowed, M gets two and the answer is wrong.
 */
private val labelMergeOneRound = sexp("label-merge")

/**
 * Only the negative eq l1 l4 tells l1 from l4: k l1 nil and k nil l4 bind no label of theirs, and a
 * nullary label would give l1 and l4 the same type. They need L's parameter, with nil polymorphic.
 */
private val nilArity =
    listOf(
        sexp("nil-arity"),
        sexp(
            "nil-arity",
            sexpDefaults.copy(
                scheduleInfo =
                    CustomSchedule(
                        listOf(
                            listOf("one", "tt", "inc", "not", "sing", "length", "k", "eq"),
                            listOf("l1", "nil", "l4"),
                        )
                            .map { it.map(::ocamlName) }
                    )
            ),
            "nil-arity-after-helpers",
        ),
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
                    ) +
                    labelMerge,
            "sexp-unsolved" to
                listOf("list-and-dict", "option", "pair").map(::sexp) + labelMergeOneRound + nilArity,
            "ocaml" to ocamlModuleGroups.map(::ocaml),
        )

    /**
     * The groups that ocaml-GROUP solves in seconds, as one chain, with their dependencies: a
     * dependency left out would make the chain solve its names again instead of being given them.
     */
    private val fastChain =
        ocamlChained(
            "ocaml-chained-fast",
            withDependencies(
                listOf(
                    "basics", "comparison", "arith", "boolean", "char", "bitwise", "str", "unit", "pair_mod", "pair",
                    "float", "bool_mod", "char_mod", "unit_mod", "option_mod", "strconv", "fun_mod",
                )
                    .map(::ocamlModuleGroup)
            )
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
