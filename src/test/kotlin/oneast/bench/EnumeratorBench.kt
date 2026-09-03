package oneast.bench

import oneast.*
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.condition.EnabledIfSystemProperty
import oneast.searchstrategies.DFSEnumerator
import query.Example
import query.Examples
import query.Name
import query.App
import testutil.unsignedExample
import testutil.ocaml.OcamlTypeParser
import util.CheckingGroundTruthOracle
import util.Logger
import util.join
import java.io.File

/**
 * Micro/macro benchmark for the enumerator's inner loop. Loads a set of OCaml stdlib modules,
 * splits examples into pos/neg with our own checker, and enumerates outlines.
 */
class EnumeratorBench {
    private fun loadFromExsFiles(exsFileNames: List<String>): Pair<List<Example>, Map<String, Type>> {
        val exsDir = File(join("src", "test", "input", "ocaml-stdlib", "exs"))
        val typesDir = File(join("src", "test", "input", "ocaml-stdlib", "types"))
        val examples = mutableListOf<Example>()
        val referencedTypesFiles = linkedSetOf<String>()
        for (name in exsFileNames) {
            val file = File(exsDir, "$name.exs")
            val lines = file.readLines()
            if (lines.isEmpty()) continue
            val firstLine = lines[0].trim()
            if (firstLine.startsWith("//")) {
                firstLine.removePrefix("//").trim().split(",").map { it.trim() }
                    .filter { it.endsWith(".types") }.forEach { referencedTypesFiles.add(it) }
            }
            lines.drop(1).forEach { line ->
                val trimmed = line.trim()
                if (trimmed.isNotBlank() && !trimmed.startsWith("//")) examples.add(unsignedExample(trimmed))
            }
        }
        val parser = OcamlTypeParser()
        val oracleTypes = buildMap {
            referencedTypesFiles.forEach { n ->
                val f = File(typesDir, n)
                if (f.isFile) putAll(parser.parseSignatures(f.readText()))
            }
        }
        return examples to oracleTypes
    }

    private fun nameIsApplied(name: String, exs: Examples): Boolean {
        fun appliedIn(ex: Example): Boolean = when (ex) {
            is Name -> false
            is App -> ((ex.fn is Name && (ex.fn as Name).name == name) || appliedIn(ex.fn) || appliedIn(ex.arg))
        }
        return exs.posNoSubexprs.any { appliedIn(it) }
    }

    fun workload(modules: List<String>): Pair<Examples, SearchState> {
        val (all, oracleTypes) = loadFromExsFiles(modules)
        val oracle = CheckingGroundTruthOracle(oracleTypes)
        val subs = all.flatMap { it.subexprs() }.toSet().filter { e -> e.names.all { it in oracleTypes } }
        val (pos, neg) = subs.partition { oracle.valid(it) }
        val minNeg = neg.filter { it.subexprs().dropLast(1).none { sub -> sub in neg } }
        val examples = Examples(pos, minNeg)
        val names = examples.names
        val seed = SearchState(
            names = names.withIndex().associate { it.value to it.index },
            types = names.map {
                if (nameIsApplied(it, examples)) Arrow(TypeHole(), TypeHole())
                else Blank(labelOnly = true)
            },
            labelArities = mapOf()
        )
        return examples to seed
    }

    @Test
    @EnabledIfSystemProperty(named = Bench.GATE, matches = ".+")
    fun enumerator() {
        val modules = Bench.list("modules", listOf("0_basics", "2_boolean", "4_arith", "8_char"))
        val limit = Bench.int("limit", 20000)
        val reps = Bench.int("reps", 3)
        val sizeBound = Bench.int("sizeBound", 60)
        val depthBound = Bench.int("depthBound", 4)
        val dump = Bench.flag("dump")
        val (examples, seed) = workload(modules)
        println("modules=$modules names=${examples.names.size} pos=${examples.posNoSubexprs.size} neg=${examples.neg.size}")
        println("total pos expr nodes=${examples.posNoSubexprs.sumOf { it.size() }} seedHoles=${seed.numFillableHoles()}")

        val cfg = Configuration(
            name = "bench", searchStrategy = ::DFSEnumerator, sizeBound = sizeBound, depthBound = depthBound,
            scheduleInfo = SingleRound, numSols = Solutions.NumSolutions(1)
        )
        repeat(reps) { r ->
            val logger = Logger(cfg, logToFile = true, logFilename = "bench.log", verbosity = 0)
            val strategy = DFSEnumerator(examples, true, true, sizeBound, depthBound, logger)
            val t0 = System.nanoTime()
            var n = 0
            var exhausted = true
            var digest = 0L
            for (c in strategy.candidates(seed)) {
                n++
                digest = digest * 1000003L + c.toString().hashCode()
                if (dump) println("  CAND $c")
                if (n >= limit) { exhausted = false; break }
            }
            val ms = (System.nanoTime() - t0) / 1_000_000.0
            println(
                ("rep $r: $n candidates${if (exhausted) " (exhausted)" else ""} in %.1f ms  " +
                        "(%.1f us/candidate) digest=$digest").format(ms, ms * 1000 / n)
            )
        }
    }
}
