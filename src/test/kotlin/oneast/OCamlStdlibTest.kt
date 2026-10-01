package oneast

import bench.Count
import bench.Stats
import dependencyanalysis.ParameterwiseDependencyAnalysis
import org.junit.jupiter.api.Disabled
import query.Example
import query.Examples
import query.Query
import testutil.loadExamples
import testutil.loadSchedule
import testutil.ocaml.*
import testutil.splitOCamlExamples
import testutil.unsignedExample
import util.*
import java.io.File
import kotlin.test.Test

class OCamlStdlibTest {
    private fun filterBySchedule(examples: Examples, schedule: CustomSchedule) =
        Examples(
            examples.posNoSubexprs.filter {
                schedule.customSchedule.flatten().containsAll(it.names)
            },
            examples.neg.filter { schedule.customSchedule.flatten().containsAll(it.names) },
        )

    private fun config(schedule: SchedulingInfo) =
        Configuration(
            sizeBound = 20,
            depthBound = 4,
            scheduleInfo = schedule,
            numSols = Solutions.NumSolutions(1)
        )

    @Test
    @Disabled
    fun `separate pos neg files and custom schedule in file`() {
        val path = join("src", "test", "input", "ocaml-stdlib", "lists-notsolved")
        val dir = File(path)
        val query = Query(loadExamples(dir), oracleFromDir(dir))
        assert(run(query, OCamlChecker(), config(loadSchedule(File(join(path, "schedule"))))).isNotEmpty())
    }

    @Test
    @Disabled
    fun `single module`() {
        val exsFileNames = listOf("4_arith", "0_basics")
        val (examples, oracleTypes) = loadFromExsFiles(exsFileNames)
        val oracle = CheckingGroundTruthOracle(oracleTypes)
        val query = Query(splitOCamlExamples(examples, oracle, OCamlChecker()), oracle)
        val sols = run(query, OCamlChecker(), config(Auto(3)))
        assert(sols.isNotEmpty())
        assert(sols.any { it.equivalentTo(stateFromContext(oracleTypes)) })
    }

    private val exsFileGroups: List<List<String>> =
        listOf(
            listOf("0_basics", "2_boolean", "4_arith", "8_char"),
            listOf("1_comparison"),
            listOf("50_list_mod"))

    /** The query for the first [iter] + 1 groups of [exsFileGroups], and its types. */
    private fun cumulativeQuery(iter: Int, committedSeed: SearchState): Pair<Query, Map<String, Type>> {
        val cumulativeFiles = exsFileGroups.subList(0, iter + 1).flatten()
        val (examplesAll, oracleTypes) = loadFromExsFiles(cumulativeFiles)
        val examples = examplesAll.flatMap {it.subexprs()}.toSet().filter{
            it.names.all { it in oracleTypes }
        }
        val oracle = CheckingGroundTruthOracle(oracleTypes)
        val query = Query(
            splitOCamlExamples(examples, oracle, OCamlChecker()),
            oracle,
            committedSeed = committedSeed
        )
        return query to oracleTypes
    }

    /** Answers like [types], but records every query [observed] answers differently. */
    private class ComparingOracle(private val types: Oracle, private val observed: Oracle) : Oracle {
        var queries = 0
        val disagreements = mutableListOf<Triple<Example, Example, Boolean>>()

        override fun equal(a: Example, b: Example): Boolean {
            queries++
            val t = types.equal(a, b)
            if (observed.equal(a, b) != t) disagreements.add(Triple(a, b, t))
            return t
        }

        override fun dummy(e: Example): Int = types.dummy(e)
    }

    /**
     * The first two rounds of the `ocaml-chained` benchmarks, solved once with each oracle. Also
     * runs the dependency analysis, the oracle's only user, with both oracles side by side, to see
     * where their answers differ.
     */
    @Test
    fun `compare oracles on first two module groups`() {
        val seeds = OracleKind.values().associateWith { SearchState.emptyState }.toMutableMap()
        for (iter in 0 until 2) {
            println("===== Round $iter: ${exsFileGroups.subList(0, iter + 1).flatten()} =====")
            val (typesQuery, oracleTypes) = cumulativeQuery(iter, SearchState.emptyState)
            val examples = typesQuery.examples
            println("${examples.posNoSubexprs.size} maximal positive, ${examples.neg.size} negative examples")

            val observed = ObservationalEquivalenceOracle(examples, MemoizedGroundTruth(OCamlChecker()))
            val comparing = ComparingOracle(typesQuery.oracle, observed)
            val arities = stateFromContext(oracleTypes).fnArities()
            val start = System.currentTimeMillis()
            val withTypes = ParameterwiseDependencyAnalysis(examples, arities, comparing)
            val elapsed = System.currentTimeMillis() - start
            val withObserved = ParameterwiseDependencyAnalysis(examples, arities, observed)
            println("Dependency analysis: ${comparing.queries} queries in ${elapsed}ms, ${comparing.disagreements.size} disagreements")
            comparing.disagreements.forEach { (a, b, t) ->
                println("  types say $a ${if (t) "==" else "!="} $b, observational says otherwise")
            }
            println("  types:         $withTypes")
            println("  observational: $withObserved")

            val solutions = OracleKind.values().associateWith { kind ->
                val (query, _) = cumulativeQuery(iter, seeds.getValue(kind))
                val t0 = System.currentTimeMillis()
                Stats.start()
                val sols = run(query, OCamlChecker(), config(Auto(3)).copy(oracle = kind))
                val counters = Stats.stop()!!.snapshot()["counters"] as Map<*, *>
                println(
                    "Search with $kind oracle: ${System.currentTimeMillis() - t0}ms, ${sols.size} solution(s), " +
                        "${counters[Count.ORACLE_CALLS.key]} oracle calls taking ${counters[Count.ORACLE_NANOS.key]}ms"
                )
                sols.firstOrNull()?.let { println("  ${it.asMap()}") }
                sols
            }
            solutions.forEach { (kind, sols) ->
                assert(sols.isNotEmpty()) { "No solution with $kind oracle at round $iter" }
                seeds[kind] = sols.first()
            }
            val (a, b) = OracleKind.values().map { seeds.getValue(it) }
            println("Solutions equivalent: ${a.equivalentTo(b)}")
        }
    }

    @Test
    fun `a batch fails if any expression in it does`() {
        val checker = OCamlChecker()
        val ok = listOf("(succ Num)", "(not true)").map { unsignedExample(it) }
        assert(checker.allValid(ok))
        assert(!checker.allValid(ok + unsignedExample("(succ true)")))
    }

    /** Input sanity check: load every .exs and .types file and run splitOCamlExamples */
    @Test
    fun `load all and split`() {
        val allExsNames = ocamlExsDir.listFiles()
            ?.filter { it.extension == "exs" && it.isFile }
            ?.map { it.nameWithoutExtension }
            ?: emptyList()

        val (examples, _) = loadFromExsFiles(allExsNames)

        val parser = OcamlTypeParser()
        val oracleTypes = buildMap {
            ocamlTypesDir.listFiles()
                ?.filter { it.extension == "types" && it.isFile }
                ?.forEach { putAll(parser.parseSignatures(it.readText())) }
        }
        val oracle = CheckingGroundTruthOracle(oracleTypes)

        splitOCamlExamples(examples, oracle, OCamlChecker())
    }
}
