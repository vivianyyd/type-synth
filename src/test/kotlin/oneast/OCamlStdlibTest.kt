package oneast

import oneast.searchstrategies.DFSEnumerator
import query.Query
import testutil.loadExamples
import testutil.ocaml.OCamlChecker
import testutil.ocaml.OcamlTypeParser
import util.CheckingGroundTruthOracle
import util.Logger
import util.io.cvc.clearCVC
import util.join
import java.io.File
import kotlin.test.Test

class OCamlStdlibTest {
    fun `split examples`() {
        val path = join("src", "test", "input", "ocaml-stdlib")
        val exs = File(join(path, "tmp"))
        val posOut = File(join(path, "pos"))
        val negOut = File(join(path, "neg"))

        val checker = OCamlChecker()
        val examples = exs.readText().lines().map { it.trim() }.filter { it.isNotEmpty() }
        val results = checker.checkAllParallel(examples)
        results.forEach {
            val out = if (it.isValid) posOut else negOut
            out.appendText(it.expression + System.lineSeparator())
        }
    }

    @Test
    fun `can reconstruct stdlib`() {
        val dir = File(join("src", "test", "input", "ocaml-stdlib", "testing"))
        val examples = loadExamples(dir)
        val parser = OcamlTypeParser()
        val oracleTypes = buildMap {
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
                scheduleInfo = Auto(5),
                numSols = Solutions.NumSolutions(1)
            )

        val logger =
            Logger(
                configuration = configuration,
                logFilename = "tmp.log",
                logToFile = true,
                verbosity = 5
            )

        clearCVC() // TODO This should really be done by the engine or someone else
        val engine =
            Engine(
                query, { e -> OCamlChecker().isValid(e.toString()).isValid }, configuration, logger
            )
        // TODO oracle should be in query, numsols in config

        engine.search().take(1).forEach { logger.log("FIRST SOLUTION: ${it.asMap()}") }
        logger.finish()
    }
}
