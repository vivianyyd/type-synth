package oneast

import oneast.searchstrategies.DFSEnumerator
import org.junit.jupiter.api.Disabled
import query.Examples
import query.Query
import testutil.loadExamples
import testutil.loadSchedule
import testutil.ocaml.OCamlChecker
import testutil.ocaml.OcamlTypeParser
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
                logFilename = "tmp.log",
                logToFile = true,
                verbosity = 5
            )

        assert(run(query, OCamlChecker(), configuration, logger).isNotEmpty())
    }
}
