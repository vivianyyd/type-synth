package oneast

import org.junit.jupiter.api.Disabled
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory
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

    @TestFactory
    fun `test sublists (factory)`(): List<DynamicTest> =
        ocamlModuleGroups.indices.map { i ->
            val task = ocamlModuleGroups[i]
            DynamicTest.dynamicTest(task.toString()) {
                val (query, expected) =
                    ocamlModulesQuery(task, fixed = ocamlModuleGroups.subList(0, i).flatten())
                val sols = run(query, OCamlChecker(), config(Auto(3)))
                assert(sols.isNotEmpty()) { "No solution found for module $task" }
                assert(sols.any { it.equivalentTo(expected) }) {
                    "None of\n${sols.lines()}\nmatch expected context\n$expected\n" +
                        sols.joinToString("\n") { "Differs in ${it.mismatches(expected)}" }
                }
            }
        }

    @Test
    fun `multiple modules`() {
        val exsFileGroups: List<List<String>> =
            listOf(
                listOf("0_basics", "2_boolean", "4_arith", "8_char"),
                listOf("1_comparison"),
                listOf("50_list_mod"))

        var committedSeed = SearchState.emptyState
        for ((iter, _) in exsFileGroups.withIndex()) {
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
            val solutions = run(query, OCamlChecker(), config(Auto(3)))
            assert(solutions.isNotEmpty()) { "No solution found at iteration $iter" }
            committedSeed = solutions.first()
        }
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

    /** arrows, hofs, modules, tuples, parameterized types incl. multiple params */
    @Test
    fun `parses signatures`() {
        fun lastResult(type: Type): Type =
            if (type is Arrow) lastResult(type.r) else type

        fun assertNamedLabel(type: Type, arity: Int) {
            assert(type is NamedLabel && type.params.size == arity) {
                "Expected a NamedLabel with $arity parameter(s) but got $type"
            }
        }

        val exsFileNames = listOf("4_arith", "0_basics", "2_boolean", "8_char", "1_comparison", "50_list_mod")
        val (_, oracleTypes) = loadFromExsFiles(exsFileNames)

        // map : ('a -> 'b) -> 'a list -> 'b list  — higher-order function + postfix `list`.
        val map = oracleTypes.getValue("map") as Arrow
        assert(map.l is Arrow) { "map's first argument should be a function type" }
        val mapRest = map.r as Arrow
        assertNamedLabel(mapRest.l, arity = 1) // 'a list
        assertNamedLabel(mapRest.r, arity = 1) // 'b list

        // partition : ('a -> bool) -> 'a list -> 'a list * 'a list  — tuple result.
        val partition = lastResult(oracleTypes.getValue("partition"))
        assertNamedLabel(partition, arity = 2) // ('a list * 'a list)

        // partition_map : ('a -> ('b, 'c) Either.t) -> 'a list -> 'b list * 'c list
        val partitionMap = oracleTypes.getValue("partition_map") as Arrow
        val either = lastResult((partitionMap.l as Arrow))
        assertNamedLabel(either, arity = 2) // ('b, 'c) Either.t

        // to_seq : 'a list -> 'a Seq.t  — single-parameter module-qualified postfix.
        val toSeq = oracleTypes.getValue("to_seq") as Arrow
        assertNamedLabel(toSeq.r, arity = 1) // 'a Seq.t

        // concat : 'a list list -> 'a list  — nested postfix application.
        val concat = oracleTypes.getValue("concat") as Arrow
        val outerList = concat.l as NamedLabel
        assertNamedLabel(outerList.params.single(), arity = 1) // inner 'a list
    }
}
