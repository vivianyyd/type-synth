package bench

import oneast.*
import query.AbstractQuery
import testutil.loadQueryFromFile
import testutil.ocaml.OCamlChecker
import testutil.ocaml.ocamlModuleGroups
import testutil.ocaml.ocamlModulesQuery
import util.GroundTruth

/** A synthesis problem, and the answer it should have if one is known. */
class Problem(val query: AbstractQuery, val groundTruth: GroundTruth, val expected: SearchState?)

/** [defaults] is the configuration a variant starts from. */
class Benchmark(val name: String, val defaults: Configuration, val load: () -> Problem)

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
            "ocaml" to
                listOf("basics", "comparison", "list", "bitwise", "float", "str")
                    .mapIndexed { i, name -> ocaml(name, i) },
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
