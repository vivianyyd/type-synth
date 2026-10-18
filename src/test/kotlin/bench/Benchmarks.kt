package bench

import oneast.*
import query.AbstractQuery
import testutil.loadQueryFromFile
import testutil.ocaml.OCamlChecker
import testutil.ocaml.loadFromExsFiles
import testutil.ocaml.ocamlModuleGroups
import testutil.ocaml.ocamlModulesQuery
import util.GroundTruth

/**
 * A synthesis problem, and the answer it should have if one is known. For a problem solved in
 * [rounds], each round's name and the names it adds, in order.
 */
class Problem(
    val query: AbstractQuery,
    val groundTruth: GroundTruth,
    val expected: SearchState?,
    val rounds: List<Pair<String, Set<String>>> = emptyList()
)

/**
 * [defaults] is the configuration a variant starts from. [load] gets the configuration the run
 * uses, for benchmarks that search while loading.
 */
class Benchmark(val name: String, val defaults: Configuration, val load: (Configuration) -> Problem)

private val sexpDefaults =
    Configuration(
        sizeBound = 20,
        depthBound = 4,
        scheduleInfo = SingleRound,
        numSols = Solutions.NumSolutions(1)
    )

private val ocamlDefaults = sexpDefaults.copy(scheduleInfo = Auto(3))

private fun sexp(file: String) =
    Benchmark(file, sexpDefaults) {
        val query = loadQueryFromFile(file)
        Problem(query, query.oracle, query.oracle.truth)
    }

/** Solves the [i]th group of modules given the true types of the groups before it. */
private fun ocaml(name: String, i: Int) =
    Benchmark("ocaml-$name", ocamlDefaults) {
        val (query, expected) =
            ocamlModulesQuery(ocamlModuleGroups[i], fixed = ocamlModuleGroups.subList(0, i).flatten())
        Problem(query, OCamlChecker(), expected)
    }

/**
 * Solves the [i]th group of modules given the search's own answer for the groups before it, as
 * OCamlStdlibTest does: each group is solved with the examples of every group so far, committed to
 * the first solution for the groups before it. The groups before it are solved while loading, so
 * they count toward loadMs and not the record's stats, and an answer they get wrong shows up in
 * the record's mismatches.
 */
private fun ocamlChained(name: String, i: Int) =
    Benchmark("ocaml-chained-$name", ocamlDefaults) { config ->
        fun query(j: Int, committed: SearchState) =
            ocamlModulesQuery(ocamlModuleGroups.subList(0, j + 1).flatten(), fixed = emptyList(), committed)

        val committed =
            (0 until i).fold(SearchState.emptyState) { committed, j ->
                run(query(j, committed).first, OCamlChecker(), config).firstOrNull()
                    ?: error("No solution for ${ocamlModuleNames[j]}, the modules before ${ocamlModuleNames[i]}")
            }
        val (query, expected) = query(i, committed)
        Problem(query, OCamlChecker(), expected, ocamlRounds(i))
    }

/** For each group of modules up to the [i]th, its name and the names it adds. */
private fun ocamlRounds(i: Int): List<Pair<String, Set<String>>> {
    val seen = mutableSetOf<String>()
    return (0..i).map { j ->
        val names = loadFromExsFiles(ocamlModuleGroups.subList(0, j + 1).flatten()).second.keys - seen
        seen += names
        ocamlModuleNames[j] to names
    }
}

private val ocamlModuleNames = listOf("basics", "comparison", "list", "bitwise", "float", "str")

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
            "ocaml-chained" to ocamlModuleNames.mapIndexed { i, name -> ocamlChained(name, i) },
        )

    val all: Map<String, Benchmark> = suites.values.flatten().associateBy { it.name }

    /** Each of [names] is a benchmark or a suite. */
    fun resolve(names: List<String>): List<Benchmark> =
        names
            .flatMap {
                suites[it] ?: listOf(all[it] ?: error("No benchmark or suite named $it. Try --list"))
            }
            .distinct()
}
