package bench

import com.squareup.moshi.JsonReader
import com.squareup.moshi.Moshi
import oneast.Configuration
import oneast.SearchState
import oneast.StateDiff
import oneast.diffTo
import oneast.nodeCount
import oneast.run
import okio.Buffer
import testutil.ocaml.OCamlGroundTruth
import util.GroundTruth
import util.stateFromContext
import java.io.BufferedWriter
import java.io.File
import java.io.FileOutputStream
import java.io.OutputStreamWriter
import java.io.Writer
import java.time.LocalDateTime
import java.time.format.DateTimeFormatter
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import java.util.concurrent.TimeoutException
import java.util.concurrent.atomic.AtomicInteger
import java.util.zip.GZIPOutputStream
import kotlin.system.exitProcess

private const val USAGE =
    """Usage: ./gradlew bench -q --args="[benchmark or suite ...] [options]"

Runs each benchmark in a JVM of its own and writes one JSON record per run to
<out>/<batch>/<benchmark>.json. A benchmark's steps are solved in order in its JVM, each
committing to the answer of the step before. With no benchmarks given, runs the sexp suite.
Any order. Quote values with spaces in single quotes.

  --variant NAME[,NAME...]  version of the search to run (default: default)
  --notes TEXT       free text recorded with every run
  --timeout SECONDS  per step, including loading it (default: 600)
  --repeat N         run each benchmark N times (default: 1)
  --jobs N           runs at once; more than 1 skews timings (default: 1)
  --trace            also write every candidate to <benchmark>.trace.jsonl.gz
  --debug            print what the search does to <benchmark>.log
  --jvm-args 'ARGS'  for each run's JVM, replacing the default (default: -Xmx4g)
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
    println("Benchmarks of more than one step:")
    Benchmarks.all.values.filter { it.steps.size > 1 }
        .forEach { b -> println("  ${b.name}: ${b.steps.joinToString { it.name }}") }
    println("Variants:")
    Variants.all.values.forEach { println("  ${it.name}: ${it.description}") }
    println("  ${Variants.DEEPEN}N: ${Variants.DEEPEN_DESCRIPTION}")
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
                synchronized(System.out) {
                    val counter = "[%2d/%d]".format(done.incrementAndGet(), runs.size)
                    val steps = (record["steps"] as? List<*>).orEmpty().filterIsInstance<Map<*, *>>()
                    for (step in steps) {
                        val name = if (b.steps.size == 1) runId else "$runId/${step["step"]}"
                        println("$counter ${summaryLine(name, step)}")
                        if (step["status"] == "wrong") print(wrongAnswer(step))
                    }
                    // The parent's verdict on a run that stopped without finishing its record
                    (record["error"] as? String)?.let {
                        println("$counter %-28s %-11s %s".format(runId, record["status"], it.lineSequence().first()))
                    }
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
    // Not finding an answer in time is a result; finding a wrong one, or breaking, is a bug
    val failed = summaries.filter { it["status"] in setOf("wrong", "error", "crashed") }
    if (failed.isNotEmpty()) {
        println("Failed: ${failed.joinToString { "${it["runId"]} (${it["status"]})" }}")
        exitProcess(1)
    }
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
    // The run times out each step itself; this is in case it can't.
    val killAfterSec = opts.timeoutSec * b.steps.size + 60
    val killed = !proc.waitFor(killAfterSec, TimeUnit.SECONDS)
    if (killed) proc.destroyForcibly().waitFor()
    // Runs print nothing unless debugging or failing
    File(dir, "$runId.log").let { if (it.length() == 0L) it.delete() }

    val recordFile = File(dir, "$runId.json")
    val status = if (killed) "timeout" else "crashed"
    val error =
        if (killed) "Killed ${killAfterSec}s in, having not finished its record"
        else "Exited with ${proc.exitValue()} without finishing its record; see $runId.log"
    if (!recordFile.isFile) {
        recordFile.writeText(
            Json.write(
                linkedMapOf(
                    "schema" to SCHEMA,
                    "runId" to runId,
                    "benchmark" to b.name,
                    "repeat" to repeat,
                    "status" to status,
                    "error" to error,
                    "steps" to emptyList<Any>(),
                    "batch" to RawJson(File(dir, "batch.json").readText()),
                ),
                pretty = true
            ) + "\n"
        )
    } else {
        // The run writes its record after each step, so one still running stopped partway: a crash,
        // the kill above, or someone killing it to cut it short. Mark it so, keeping the steps it
        // finished. See "A run that stops early" in bench/README.md
        val fields = readFields(recordFile)
        if (fields["status"]?.let { (it as RawJson).text.trim() } == "\"running\"") {
            recordFile.writeText(Json.write(fields + mapOf("status" to status, "error" to error), pretty = true) + "\n")
        }
    }
    return Moshi.Builder().build().adapter(Map::class.java).fromJson(recordFile.readText())!!
}

/** The top-level fields of a record, each as the JSON it was written as. */
private fun readFields(file: File): Map<String, Any?> {
    val reader = JsonReader.of(Buffer().writeUtf8(file.readText()))
    val fields = linkedMapOf<String, Any?>()
    reader.beginObject()
    while (reader.hasNext()) fields[reader.nextName()] = RawJson(reader.nextSource().use { it.readUtf8() })
    reader.endObject()
    return fields
}

/** One step of a run, called [name]. */
private fun summaryLine(name: String, step: Map<*, *>): String {
    val stats = step["stats"] as? Map<*, *>
    val counters = stats?.get("counters") as? Map<*, *>
    fun count(key: String) = (counters?.get(key) as? Number)?.toLong() ?: 0
    val time = (stats?.get("wallMs") as? Number)?.let { "%8.1fs".format(it.toDouble() / 1000) } ?: " ".repeat(9)
    return "%-28s %-11s %s  candidates=%d prunedPos=%d prunedNeg=%d solverCalls=%d%s".format(
        name, step["status"], time,
        count("candidates"), count("prunedPos"), count("prunedNeg"), count("solverCalls"),
        bestScore(step)?.let { "  ${describeScore(it)}" } ?: ""
    )
}

/** The score of the solution closest to the expected answer, if there is one to compare with. */
private fun bestScore(step: Map<*, *>): Map<*, *>? =
    (step["scores"] as? List<*>)?.filterIsInstance<Map<*, *>>()?.minByOrNull { (it["cost"] as Number).toInt() }

private fun describeScore(score: Map<*, *>): String {
    fun int(key: String) = (score[key] as Number).toInt()
    return "exact=%d/%d cost=%d/%d".format(int("exactNames"), int("names"), int("cost"), int("expectedSize"))
}

/** Each solution of a step next to the expected answer, with the names whose types differ marked. */
private fun wrongAnswer(step: Map<*, *>): String {
    val expected = step["expected"] as Map<*, *>
    val solutions = step["solutions"] as List<*>
    val scores = step["scores"] as List<*>
    return solutions.indices.joinToString("") { i ->
        val solution = solutions[i] as Map<*, *>
        val score = scores[i] as Map<*, *>
        val byName = score["byName"] as Map<*, *>
        val names = solution.keys.map { it.toString() }
        val nameWidth = maxOf(4, names.maxOf { it.length })
        val gotWidth = maxOf(8, solution.values.maxOf { it.toString().length })
        val row = "        %s %-${nameWidth}s  %4s  %-${gotWidth}s  %s\n"
        (if (solutions.size > 1) "        Solution ${i + 1}: ${describeScore(score)}\n" else "") +
            row.format(" ", "name", "cost", "returned", "expected") +
            names.joinToString("") { n ->
                val cost = (byName[n] as? Map<*, *>)?.get("cost")?.let { (it as Number).toInt() }
                row.format(if (cost != null && cost > 0) "*" else " ", n, cost ?: "-", solution[n], expected[n])
            }
    } + "        (* differs from expected)\n"
}

private const val SCHEMA = 2

private fun SearchState.toJson(): Map<String, String> = asMap().mapValues { it.value.toString() }

/**
 * How far a solution is from [expected] on [names] only: the cost overall and per name, and the
 * names that match.
 */
private fun StateDiff.toJson(expected: SearchState, names: List<String>): Map<String, Any?> {
    fun expectedSize(name: String) = expected.names[name]?.let { expected.types[it].nodeCount() } ?: 0
    val own = StateDiff(
        cost = names.sumOf { costByName[it] ?: 0 },
        expectedSize = names.sumOf(::expectedSize),
        costByName = names.associateWith { costByName[it] ?: 0 }
    )
    return linkedMapOf(
        "cost" to own.cost,
        "expectedSize" to own.expectedSize,
        "ratio" to own.ratio,
        "exactNames" to own.costByName.count { it.value == 0 },
        "names" to own.costByName.size,
        "byName" to
            own.costByName.mapValues { (name, c) -> linkedMapOf("cost" to c, "expectedSize" to expectedSize(name)) },
    )
}

/** Whether a run is still going, and the step it's on, as far as the step's timeout needs to know. */
private class Progress {
    @Volatile var loadMs: Double? = null
    @Volatile var recording: Recording? = null
}

/** Runs one benchmark's steps in this JVM, writing its record after each. */
private fun runOne(opts: Options) {
    val dir = opts.dir!!
    val runId = opts.runId!!
    val benchmark = Benchmarks.all[opts.child!!] ?: error("No benchmark ${opts.child}")
    val variant = Variants.get(opts.variant)
    val config = variant.configure(benchmark.defaults)
    // One for the whole run, shared by its steps
    val groundTruth = (variant.ocamlGroundTruth ?: OCamlGroundTruth.default).create()
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

    val steps = mutableListOf<Map<String, Any?>>()

    /** Until [done], the run's status is running. Readers never see half a record. */
    fun writeRecord(done: Boolean) {
        // The first step that went wrong or didn't finish, if any
        val status =
            if (!done) "running"
            else (steps.firstOrNull { it["status"] !in setOf("correct", "solved") } ?: steps.last())["status"]
        val record = base + mapOf(
            "status" to status,
            "steps" to steps,
            "batch" to RawJson(File(dir, "batch.json").readText())
        )
        val tmp = File(dir, "$runId.json.tmp")
        tmp.writeText(Json.write(record, pretty = true) + "\n")
        tmp.renameTo(File(dir, "$runId.json"))
    }

    // Steps are solved on a worker so that this thread can time them out
    val worker = Executors.newSingleThreadExecutor { Thread(it, "step").apply { isDaemon = true } }
    var committed = SearchState.emptyState
    val order = mutableListOf<String>() // every name solved so far, by the step that solved it
    for ((i, step) in benchmark.steps.withIndex()) {
        val progress = Progress()
        val solving = worker.submit<Pair<Map<String, Any?>, SearchState?>> {
            solveStep(step, committed, order, config, groundTruth, trace, progress)
        }
        val (record, solution) =
            try {
                solving.get(opts.timeoutSec, TimeUnit.SECONDS)
            } catch (e: TimeoutException) {
                // The worker may still be writing the trace; closing it again is a no-op
                val stats = progress.recording?.let { r -> synchronized(r) { trace?.close(); r.snapshot() } }
                trace?.close()
                steps += linkedMapOf(
                    "step" to step.name, "status" to "timeout", "loadMs" to progress.loadMs, "stats" to stats
                )
                writeRecord(done = true)
                // Exiting rather than halting runs the hook that deletes the solver's files.
                exitProcess(0)
            }
        steps += record
        writeRecord(done = solution == null || i == benchmark.steps.lastIndex)
        committed = solution ?: break
    }
    trace?.close()
    exitProcess(0)
}

/**
 * Loads [step] given the answer [committed] to so far, solves it, and compares its answer with the
 * expected one. Returns the step's record, and the solution to commit to, if there is one. [order]
 * is every name the steps before it solved, in the order they solved them; this adds the step's.
 * [groundTruth] is the run's, which [step] may ignore.
 */
private fun solveStep(
    step: Step,
    committed: SearchState,
    order: MutableList<String>,
    config: Configuration,
    groundTruth: GroundTruth,
    trace: Writer?,
    progress: Progress,
): Pair<Map<String, Any?>, SearchState?> {
    try {
        val loadStart = System.nanoTime()
        val problem = step.load(committed, groundTruth)
        progress.loadMs = (System.nanoTime() - loadStart) / 1_000_000.0

        val recording = Stats.start(trace, step.name)
        progress.recording = recording
        val solutions =
            try {
                run(problem.query, problem.groundTruth, config)
            } finally {
                Stats.stop()
            }
        val stats = recording.snapshot()

        // The step's own names: the ones it wasn't given
        val seed = problem.query.committedSeed.names.keys
        val names = solutions.firstOrNull()?.names?.keys?.filter { it !in seed }.orEmpty()
        // The expected answer, in the order the names were solved in, so that a label conflict is
        // charged to the step that introduced it. The expected context can have names that no
        // example mentions, which aren't solved for
        val expected =
            problem.expected?.let { e ->
                val inOrder = seed.filter { it !in order } + order + names
                stateFromContext(inOrder.filter { it in e.names }.associateWith { e.typeOf(it) })
            }
        val scores = expected?.let { e -> solutions.map { s -> e.diffTo(s).toJson(e, names) } }
        order += names
        val status =
            when {
                solutions.isEmpty() -> "no-solution"
                scores == null -> "solved"
                scores.any { it["cost"] == 0 } -> "correct"
                else -> "wrong"
            }
        val record =
            linkedMapOf(
                "step" to step.name,
                "status" to status,
                "loadMs" to progress.loadMs,
                "groundTruth" to problem.groundTruth::class.simpleName,
                "names" to names,
                "solutions" to solutions.map { s -> s.toJson().filterKeys { it in names } },
                "expected" to expected?.toJson()?.filterKeys { it in names },
                "scores" to scores,
                "stats" to stats,
            )
        return record to solutions.firstOrNull()
    } catch (e: Throwable) {
        e.printStackTrace()
        val record =
            linkedMapOf(
                "step" to step.name,
                "status" to "error",
                "loadMs" to progress.loadMs,
                "error" to e.stackTraceToString(),
                "stats" to progress.recording?.snapshot(),
            )
        return record to null
    }
}
