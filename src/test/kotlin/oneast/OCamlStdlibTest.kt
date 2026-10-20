package oneast

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

    /** Input sanity check: load every .exs and .types file and run splitOCamlExamples */
    @Test
    fun `load all and split`() {
        val allExsNames = ocamlExsDir.listFiles()
            ?.filter { it.extension == "exs" && it.isFile }
            ?.map { it.nameWithoutExtension }
            ?: emptyList()

        val (examples, _, labels) = loadFromExsFiles(allExsNames)

        val parser = OcamlTypeParser()
        val oracleTypes = buildMap {
            ocamlTypesDir.listFiles()
                ?.filter { it.extension == "types" && it.isFile }
                ?.forEach { putAll(parser.parseSignatures(it.readText())) }
        }
        val oracle = CheckingGroundTruthOracle(oracleTypes)

        splitOCamlExamples(examples, oracle, OCamlChecker(labels = labels))
    }
}
