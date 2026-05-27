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

    @Test
    @Disabled
    fun `can reconstruct stdlib`() {
        val path = join("src", "test", "input", "ocaml-stdlib", "primitive-operations-solved")
        val dir = File(path)
        val examples = loadExamples(dir)
        val schedule = loadSchedule(File(join(path, "schedule")))

        val oracleTypes = buildMap {
            val parser = OcamlTypeParser()
            dir.listFiles()
                ?.filter { it.extension == "types" && it.isFile }
                ?.forEach { file -> putAll(parser.parseSignatures(file.readText())) }
        }
        val oracle = CheckingGroundTruthOracle(oracleTypes)
        val query = Query(examples, oracle)

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
                logFilename = "ocaml-willBeOverwritten.log",
                logToFile = true,
                verbosity = 5
            )

        assert(run(query, OCamlChecker(), configuration, logger).isNotEmpty())
    }

    /**
     * Loads examples and oracle types from a list of .exs files.
     *
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

    @Test
//    @Disabled
    fun `can reconstruct from exs files`() {
        val exsFileNames = listOf("4_arith", "0_basics") // , "2_boolean")

        val (examples, oracleTypes) = loadFromExsFiles(exsFileNames)
        val oracle = CheckingGroundTruthOracle(oracleTypes)
        val query = Query(splitOCamlExamples(examples, oracle, OCamlChecker()), oracle)

        val configuration =
            Configuration(
                name = "OCaml Stdlib (exs)",
                searchStrategy = ::DFSEnumerator,
                sizeBound = 20,
                depthBound = 4,
                scheduleInfo = Auto(3),
                numSols = Solutions.NumSolutions(1)
            )

        val logger =
            Logger(
                configuration = configuration,
                logFilename = "ocaml-exs-willBeOverwritten.log",
                logToFile = true,
                verbosity = 5
            )

        assert(run(query, OCamlChecker(), configuration, logger).isNotEmpty())
    }
}
