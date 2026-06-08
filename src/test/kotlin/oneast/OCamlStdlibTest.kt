package oneast

import oneast.searchstrategies.DFSEnumerator
import org.junit.jupiter.api.Disabled
import query.Example
import query.Examples
import query.Query
import testutil.loadExamples
import testutil.loadSchedule
import testutil.ocaml.OCamlChecker
import testutil.ocaml.OcamlTypeParser
import testutil.splitOCamlExamples
import testutil.unsignedExample
import util.CheckingGroundTruthOracle
import util.Logger
import util.join
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

    private fun oracleFromDir(dir: File) = CheckingGroundTruthOracle(buildMap {
        val parser = OcamlTypeParser()
        dir.listFiles()
            ?.filter { it.extension == "types" && it.isFile }
            ?.forEach { file -> putAll(parser.parseSignatures(file.readText())) }
    })

    /**
     * Loads examples and oracle types from a list of .exs files.
     * Each .exs file's first line must be a comment listing the .types files it depends on, e.g.:
     *   // 0_basics.types, 4_arith.types
     * All subsequent non-comment, non-blank lines are treated as examples.
     */
    private fun loadFromExsFiles(exsFileNames: List<String>): Pair<List<Example>, Map<String, Type>> {
        val exsDir = File(join("src", "test", "input", "ocaml-stdlib", "exs"))
        val typesDir = File(join("src", "test", "input", "ocaml-stdlib", "types"))

        val examples = mutableListOf<Example>()
        val referencedTypesFiles = linkedSetOf<String>()

        for (name in exsFileNames) {
            val file = File(exsDir, if (name.endsWith(".exs")) name else "$name.exs")
            val lines = file.readLines()
            if (lines.isEmpty()) continue
            val firstLine = lines[0].trim()
            if (firstLine.startsWith("//")) {
                firstLine.removePrefix("//").trim()
                    .split(",")
                    .map { it.trim() }
                    .filter { it.endsWith(".types") }
                    .forEach {
                        if (it.substringBefore(".types") !in exsFileNames)
                            println("Warning in module $name: Dependency $it is not in provided files, adding its type signatures without its examples")
                        referencedTypesFiles.add(it)
                    }
            }
            lines.drop(1).forEach { line ->
                val trimmed = line.trim()
                if (trimmed.isNotBlank() && !trimmed.startsWith("//")) {
                    examples.add(unsignedExample(trimmed))
                }
            }
        }
        val parser = OcamlTypeParser()
        val oracleTypes = buildMap {
            referencedTypesFiles.forEach { typesFileName ->
                val typesFile = File(typesDir, typesFileName)
                if (typesFile.isFile) putAll(parser.parseSignatures(typesFile.readText()))
            }
        }
        return examples to oracleTypes
    }

    private fun configLogger(schedule: SchedulingInfo, iter: Int? = null): Pair<Configuration, Logger> {
        val configuration =
            Configuration(
                name = "OCaml Stdlib",
                searchStrategy = ::DFSEnumerator,
                sizeBound = 20,
                depthBound = 4,
                scheduleInfo = schedule,
                numSols = Solutions.NumSolutions(1)
            )

        val logger =
            Logger(
                configuration = configuration,
                logFilename = "ocaml-tmp${if (iter != null) "-$iter" else ""}.log",
                logToFile = true,
                verbosity = 5
            )
        return configuration to logger
    }

    @Test
    @Disabled
    fun `separate pos neg files and custom schedule in file`() {
        val path = join("src", "test", "input", "ocaml-stdlib", "lists-notsolved")
        val dir = File(path)
        val query = Query(loadExamples(dir), oracleFromDir(dir))
        val (configuration, logger) = configLogger(loadSchedule(File(join(path, "schedule"))))
        assert(run(query, OCamlChecker(), configuration, logger).isNotEmpty())
    }

    @Test
//    @Disabled
    fun `single module`() {
        val exsFileNames = listOf("4_arith", "0_basics") // , "2_boolean")
        val (examples, oracleTypes) = loadFromExsFiles(exsFileNames)
        val oracle = CheckingGroundTruthOracle(oracleTypes)
        val query = Query(splitOCamlExamples(examples, oracle, OCamlChecker()), oracle)
        val (configuration, logger) = configLogger(Auto(3))
        assert(run(query, OCamlChecker(), configuration, logger).isNotEmpty())
    }

    @Test
    fun `multiple modules`() {
        val exsFileGroups: List<List<String>> = listOf(
            // 0_basics.types, 1_comparison.types, 4_arith.types, 8_char.types, 50_list_mod.exs
            listOf("4_arith", "0_basics", "2_boolean", "8_char", "1_comparison"),// "7_str", ),
            listOf("50_list_mod")
//            listOf("5_bitwise"),
//            listOf("6_float")
        )

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
            val (configuration, logger) = configLogger(Auto(3), iter)
            val solutions = run(query, OCamlChecker(), configuration, logger)
            assert(solutions.isNotEmpty()) { "No solution found at iteration $iter" }
            committedSeed = solutions.first()
        }
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
