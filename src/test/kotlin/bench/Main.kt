package bench

import com.squareup.moshi.Moshi
import oneast.SearchState
import oneast.mismatches
import oneast.run
import util.stateFromContext
import java.io.BufferedWriter
import java.io.File
import java.io.FileOutputStream
import java.io.OutputStreamWriter
import java.time.LocalDateTime
import java.time.format.DateTimeFormatter
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import java.util.concurrent.atomic.AtomicBoolean
import java.util.concurrent.atomic.AtomicInteger
import java.util.zip.GZIPOutputStream
import kotlin.concurrent.thread
import kotlin.system.exitProcess

private const val USAGE =
    """Usage: ./gradlew bench --args="[options] [benchmark or suite ...]"

Runs each benchmark in a JVM of its own and writes one JSON record per run to
<out>/<batch>/<benchmark>.json. With no benchmarks given, runs the sexp suite.

  --variant NAME     version of the search to run (default: default)
  --notes TEXT       free text recorded with every run
  --timeout SECONDS  per run, including loading the benchmark (default: 600)
  --repeat N         run each benchmark N times (default: 1)
  --jobs N           runs at once; more than 1 skews timings (default: 1)
  --trace            also write every candidate to <benchmark>.trace.jsonl.gz
  --debug            print what the search does to <benchmark>.log
  --jvm-args "ARGS"  for each run's JVM (default: -Xmx4g)
  --out DIR          (default: bench-results)
  --list             list benchmarks, suites and variants"""

private class Options(
    val targets: List<String>,
    val variant: String,
    val notes: String,
    val timeoutSec: Long,
    val repeat: Int,
    val jobs: Int,
    val trace: Boolean,
    val debug: Boolean,
    val jvmArgs: List<String>,
    val out: File,
    val list: Boolean,
    // Only for the JVM running one benchmark
    val child: String?,
    val dir: File?,
    val runId: String?,
    val repeatIndex: Int,
) {
    companion object {
        fun parse(args: Array<String>): Options {
            val targets = mutableListOf<String>()
            val flags = mutableMapOf<String, String>()
            val switches = setOf("--trace", "--debug", "--list", "--help")
            var i = 0
            while (i < args.size) {
                val a = args[i]
                when {
                    a in switches -> flags[a] = "true"
                    a.startsWith("--") -> {
                        require(i + 1 < args.size) { "$a needs a value\n$USAGE" }
                        flags[a] = args[++i]
                    }
                    else -> targets.add(a)
                }
                i++
            }
            if ("--help" in flags) {
                println(USAGE)
                exitProcess(0)
            }
            val known =
                switches + setOf(
                    "--variant", "--notes", "--timeout", "--repeat", "--jobs", "--jvm-args", "--out",
                    "--child", "--dir", "--run-id", "--repeat-index"
                )
            flags.keys.firstOrNull { it !in known }?.let { error("Unknown option $it\n$USAGE") }
            return Options(
                targets = targets,
                variant = flags["--variant"] ?: "default",
                notes = flags["--notes"] ?: "",
                timeoutSec = flags["--timeout"]?.toLong() ?: 600,
                repeat = flags["--repeat"]?.toInt() ?: 1,
                jobs = flags["--jobs"]?.toInt() ?: 1,
                trace = "--trace" in flags,
                debug = "--debug" in flags,
                jvmArgs = (flags["--jvm-args"] ?: "-Xmx4g").split(" ").filter { it.isNotBlank() },
                out = File(flags["--out"] ?: "bench-results"),
                list = "--list" in flags,
                child = flags["--child"],
                dir = flags["--dir"]?.let { File(it) },
                runId = flags["--run-id"],
                repeatIndex = flags["--repeat-index"]?.toInt() ?: 0,
            )
        }
    }
}

fun main(args: Array<String>) {
    val opts = Options.parse(args)
    when {
        opts.list -> list()
        opts.child != null -> runOne(opts)
        else -> runBatch(opts)
    }
}

private fun list() {
    println("Suites:")
    Benchmarks.suites.forEach { (name, bs) -> println("  $name: ${bs.joinToString { it.name }}") }
    println("Variants:")
    Variants.all.values.forEach { println("  ${it.name}: ${it.description}") }
}

private fun runBatch(opts: Options) {
    val benchmarks = Benchmarks.resolve(opts.targets.ifEmpty { listOf("sexp") })
    val variant = Variants.get(opts.variant)
    val git = GitInfo.read()
    val startedAt = LocalDateTime.now()
    val batchId =
        "${startedAt.format(DateTimeFormatter.ofPattern("yyyy-MM-dd_HHmmss"))}_" +
            "${git.short}${if (git.dirty) "+dirty" else ""}_${variant.name}"
    val dir = File(opts.out, batchId).apply { mkdirs() }
    val patchFile = if (git.dirty) "changes.patch" else null
    patchFile?.let { File(dir, it).writeText(git.patch + "\n") }
    File(dir, "batch.json")
        .writeText(
            Json.write(
                linkedMapOf(
                    "batchId" to batchId,
                    "startedAt" to startedAt.toString(),
                    "variant" to variant.name,
                    "variantDescription" to variant.description,
                    "notes" to opts.notes,
                    "benchmarks" to benchmarks.map { it.name },
                    "repeat" to opts.repeat,
                    "timeoutSec" to opts.timeoutSec,
                    "jobs" to opts.jobs,
                    "trace" to opts.trace,
                    "git" to git.toJson(patchFile),
                    "machine" to machineJson(opts.jvmArgs),
                ),
                pretty = true
            ) + "\n"
        )

    println("Batch $batchId: ${benchmarks.size} benchmarks, variant ${variant.name}, commit ${git.short}")
    if (git.dirty) println("  Uncommitted changes are saved to changes.patch")
    if (opts.jobs > 1) println("  Running ${opts.jobs} at once, so timings are not comparable")

    val runs = benchmarks.flatMap { b -> (0 until opts.repeat).map { b to it } }
    val done = AtomicInteger()
    val pool = Executors.newFixedThreadPool(opts.jobs)
    val summaries =
        runs.map { (b, r) ->
            pool.submit<Map<*, *>> {
                val runId = if (opts.repeat > 1) "${b.name}.$r" else b.name
                val record = runChild(opts, b, runId, r, dir)
                val line = summaryLine(record)
                synchronized(System.out) {
                    println("[%2d/%d] %s".format(done.incrementAndGet(), runs.size, line))
                    if (record["status"] == "wrong") print(wrongAnswer(record))
                }
                record
            }
        }
            .map { it.get() }
    pool.shutdown()

    val statuses = summaries.groupingBy { it["status"] }.eachCount()
    println("\n$statuses")
    println("Results in $dir")
    println("  python3 bench/analyze.py show $dir")
}

/** Runs one benchmark in a JVM of its own, and returns its record. */
private fun runChild(opts: Options, b: Benchmark, runId: String, repeat: Int, dir: File): Map<*, *> {
    val cmd =
        listOf(javaExecutable()) + opts.jvmArgs +
            listOf("-cp", System.getProperty("java.class.path"), "bench.MainKt") +
            listOf(
                "--child", b.name,
                "--dir", dir.path,
                "--run-id", runId,
                "--repeat-index", "$repeat",
                "--variant", opts.variant,
                "--timeout", "${opts.timeoutSec}",
            ) +
            (if (opts.trace) listOf("--trace") else emptyList()) +
            (if (opts.debug) listOf("--debug") else emptyList())
    val proc =
        ProcessBuilder(cmd)
            .redirectErrorStream(true)
            .redirectOutput(File(dir, "$runId.log"))
            .start()
    // The run times itself out; this is in case it can't.
    if (!proc.waitFor(opts.timeoutSec + 60, TimeUnit.SECONDS)) proc.destroyForcibly().waitFor()
    // Runs print nothing unless debugging or failing
    File(dir, "$runId.log").let { if (it.length() == 0L) it.delete() }

    val recordFile = File(dir, "$runId.json")
    if (!recordFile.isFile) {
        recordFile.writeText(
            Json.write(
                linkedMapOf(
                    "schema" to SCHEMA,
                    "runId" to runId,
                    "benchmark" to b.name,
                    "repeat" to repeat,
                    "status" to "crashed",
                    "error" to "Exited with ${proc.exitValue()} without a record; see $runId.log",
                    "batch" to RawJson(File(dir, "batch.json").readText()),
                ),
                pretty = true
            )
        )
    }
    return Moshi.Builder().build().adapter(Map::class.java).fromJson(recordFile.readText())!!
}

private fun summaryLine(record: Map<*, *>): String {
    val stats = record["stats"] as? Map<*, *>
    val counters = stats?.get("counters") as? Map<*, *>
    fun count(key: String) = (counters?.get(key) as? Number)?.toLong() ?: 0
    val time = (stats?.get("wallMs") as? Number)?.let { "%8.1fs".format(it.toDouble() / 1000) } ?: " ".repeat(9)
    return "%-24s %-11s %s  candidates=%d prunedPos=%d prunedNeg=%d solverCalls=%d".format(
        record["runId"], record["status"], time,
        count("candidates"), count("prunedPos"), count("prunedNeg"), count("solverCalls")
    )
}

/** Each solution next to the expected answer, with the names whose types differ marked. */
private fun wrongAnswer(record: Map<*, *>): String {
    val expected = record["expected"] as Map<*, *>
    val solutions = record["solutions"] as List<*>
    val mismatches = record["mismatches"] as List<*>
    return solutions.indices.joinToString("") { i ->
        val solution = solutions[i] as Map<*, *>
        val differs = mismatches[i] as List<*>
        val names = solution.keys.map { it.toString() }
        val nameWidth = maxOf(4, names.maxOf { it.length })
        val gotWidth = maxOf(8, solution.values.maxOf { it.toString().length })
        val row = "        %s %-${nameWidth}s  %-${gotWidth}s  %s\n"
        (if (solutions.size > 1) "        Solution ${i + 1}:\n" else "") +
            row.format(" ", "name", "returned", "expected") +
            names.joinToString("") { n ->
                row.format(if (n in differs) "*" else " ", n, solution[n], expected[n])
            }
    } + "        (* differs from expected)\n"
}

private const val SCHEMA = 1

private fun SearchState.toJson(): Map<String, String> = asMap().mapValues { it.value.toString() }

/** Runs one benchmark in this JVM and writes its record. */
private fun runOne(opts: Options) {
    val dir = opts.dir!!
    val runId = opts.runId!!
    val benchmark = Benchmarks.all[opts.child!!] ?: error("No benchmark ${opts.child}")
    val config = Variants.get(opts.variant).configure(benchmark.defaults)
    Debug.enabled = opts.debug

    val base =
        linkedMapOf<String, Any?>(
            "schema" to SCHEMA,
            "runId" to runId,
            "benchmark" to benchmark.name,
            "repeat" to opts.repeatIndex,
            "config" to config.toJson(),
        )

    val trace =
        if (opts.trace)
            BufferedWriter(
                OutputStreamWriter(
                    GZIPOutputStream(FileOutputStream(File(dir, "$runId.trace.jsonl.gz"))), Charsets.UTF_8
                ),
                1 shl 16
            )
        else null

    val written = AtomicBoolean(false)
    var recording: Recording? = null

    /** Returns false if the record was already written, by the timeout. */
    fun finish(fields: Map<String, Any?>): Boolean {
        if (!written.compareAndSet(false, true)) return false
        val stats = recording?.let { r -> synchronized(r) { trace?.close(); r.snapshot() } }
        val record = base + fields + mapOf("stats" to stats, "batch" to RawJson(File(dir, "batch.json").readText()))
        val tmp = File(dir, "$runId.json.tmp")
        tmp.writeText(Json.write(record, pretty = true) + "\n")
        tmp.renameTo(File(dir, "$runId.json"))
        return true
    }

    thread(isDaemon = true, name = "timeout") {
        Thread.sleep(opts.timeoutSec * 1000)
        // Exiting rather than halting runs the hook that deletes the solver's files.
        if (finish(mapOf("status" to "timeout"))) exitProcess(0)
    }

    val fields =
        try {
            val loadStart = System.nanoTime()
            val problem = benchmark.load()
            base["loadMs"] = (System.nanoTime() - loadStart) / 1_000_000.0

            recording = Stats.start(trace)
            val solutions = run(problem.query, problem.groundTruth, config)
            Stats.stop()

            val expected = problem.expected
            // The expected context can have names that no example mentions, which aren't solved for
            val mismatches =
                expected?.let { e ->
                    solutions.map { s ->
                        s.mismatches(stateFromContext(e.asMap().filterKeys { it in s.names }))
                            ?: listOf("different names")
                    }
                }
            linkedMapOf(
                "status" to
                    when {
                        solutions.isEmpty() -> "no-solution"
                        mismatches == null -> "solved"
                        mismatches.any { it.isEmpty() } -> "correct"
                        else -> "wrong"
                    },
                "matchesExpected" to mismatches?.let { m -> m.any { it.isEmpty() } },
                "solutions" to solutions.map { it.toJson() },
                "expected" to expected?.toJson(),
                "mismatches" to mismatches,
            )
        } catch (e: Throwable) {
            e.printStackTrace()
            mapOf("status" to "error", "error" to e.stackTraceToString())
        }
    if (!finish(fields)) Thread.sleep(Long.MAX_VALUE) // The timeout is writing the record and will exit.
    exitProcess(0)
}
