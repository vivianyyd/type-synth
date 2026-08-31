package oneast.bench

import oneast.*
import oneast.searchstrategies.DFSEnumerator
import testutil.loadQueryFromFile
import util.GroundTruth
import util.Logger

/** Runs one of the .sexp synthesis queries end to end, with timing. */
object SexpBench {
    @JvmStatic
    fun main(args: Array<String>) {
        val name = if (args.isNotEmpty()) args[0] else "hofs"
        val query = loadQueryFromFile(name)
        val truth: GroundTruth = query.oracle
        val cfg = Configuration(
            name = name, searchStrategy = ::DFSEnumerator, sizeBound = 20, depthBound = 4,
            scheduleInfo = SingleRound, numSols = Solutions.NumSolutions(1)
        )
        val logger = Logger(cfg, logToFile = true, logFilename = "$name-bench.log", verbosity = 5)
        val t0 = System.nanoTime()
        val sols = run(query, truth, cfg, logger)
        println("$name: ${sols.size} solutions in ${(System.nanoTime() - t0) / 1_000_000} ms")
        sols.forEach { println("  $it") }
    }
}
