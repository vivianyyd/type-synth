package bench

import java.io.Writer
import java.util.concurrent.atomic.AtomicLongArray

/** What a query spends its time on. Anything outside of these is charged to no phase. */
enum class Phase(val key: String) {
    OUTLINE("outline"),
    ARITY("arity"),
    CONCRETIZE("concretize"),
    CEGIS("cegis"),
}

/** [nanos] counts are written out in milliseconds, under [key]. */
enum class Count(val key: String, val nanos: Boolean = false) {
    /** Expansions of a hole, whether or not they pass the positive examples. */
    CANDIDATES("candidates"),
    /** States that fail to unify with the positive examples. */
    PRUNED_POS("prunedPos"),
    /** States retried with labels that clashed blanked out, rather than pruned. */
    RELABELED("relabeled"),
    /** States in which some negative example type-checks however the holes are filled. */
    PRUNED_NEG("prunedNeg"),
    /** Finished states rejected by the negative examples after concretizing. */
    PRUNED_NEG_FINAL("prunedNegFinal"),
    /** Outlines produced before label classes are assigned. */
    OUTLINES("outlines"),
    /** Outlines whose blanks could not be given label classes. */
    PRUNED_LABEL_CLASSES("prunedLabelClasses"),
    /** Outlines with no label arities that fit. */
    ARITY_UNSAT("arityUnsat"),
    /** Seeds handed to concretization, one per choice of label arities. */
    SEEDS("seeds"),
    SOLVER_CALLS("solverCalls"),
    /** Summed across the threads that call the solver, so it can exceed the wall-clock time. */
    SOLVER_NANOS("solverMs", nanos = true),
    SOLUTIONS("solutions"),
    CEGIS_POS("cegisPos"),
    CEGIS_NEG("cegisNeg"),
}

/** The time and counts charged to one phase of one query. */
class Cell(val query: Int, val phase: Phase?) {
    val counts = AtomicLongArray(Count.values().size)
    /** Only the thread driving the search touches this. */
    var nanos = 0L
}

/** One synthesis problem the engine hands to the search: one round, at one outer depth bound. */
class QueryStats(
    val id: Int,
    val round: Int,
    val outerDepth: Int,
    val names: List<String>,
    val numPos: Int,
    val numNeg: Int,
) {
    val cells = Phase.values().map { Cell(id, it) }
}

/**
 * Counts and times what the search does, per phase of each query. Records nothing unless a
 * [Recording] is started, so tests that don't benchmark pay only a null check per call.
 *
 * Time is charged to whichever phase is running, not to whichever phase created a lazy sequence.
 * [phase] charges an eager block, and [inPhase] charges every step of a sequence's iterator. They
 * nest, and time is exclusive: while an inner phase runs, the outer one's clock is paused.
 *
 * All of this is meant for one run per JVM. Phases are entered and left by the thread driving the
 * search only; counters may be bumped from any thread, and go to the phase running at the time.
 */
object Stats {
    @JvmStatic
    var recording: Recording? = null
        private set

    fun start(trace: Writer? = null): Recording = Recording(trace).also { recording = it }

    fun stop(): Recording? = recording.also { recording = null }

    fun inc(c: Count) {
        recording?.current?.counts?.incrementAndGet(c.ordinal)
    }

    fun add(c: Count, n: Long) {
        recording?.current?.counts?.addAndGet(c.ordinal, n)
    }

    /** Returns the id to charge the query's phases to, or -1 when not recording. */
    fun newQuery(round: Int, outerDepth: Int, names: List<String>, numPos: Int, numNeg: Int): Int =
        recording?.newQuery(round, outerDepth, names, numPos, numNeg) ?: -1

    /** Never yield from inside [block]: the phase would stay entered while the caller runs. */
    inline fun <T> phase(query: Int, phase: Phase, block: () -> T): T {
        val r = recording ?: return block()
        r.enter(r.cell(query, phase))
        try {
            return block()
        } finally {
            r.exit()
        }
    }

    fun event(kind: String, fields: Map<String, Any?> = emptyMap()) {
        recording?.event(kind, fields)
    }

    /** Run-level facts, such as the schedule the engine decided on. */
    fun note(key: String, value: Any?) {
        recording?.info?.put(key, value)
    }

    /** Writes [state] to the candidate trace. Builds nothing unless tracing. */
    inline fun trace(kind: String, state: () -> Any) {
        val r = recording ?: return
        if (r.trace != null) r.writeTrace(kind, state())
    }
}

/** Charges every step of this sequence's iterator to [phase] of [query]. */
fun <T> Sequence<T>.inPhase(query: Int, phase: Phase): Sequence<T> {
    val seq = this
    return Sequence {
        val r = Stats.recording ?: return@Sequence seq.iterator()
        val cell = r.cell(query, phase)
        val it = seq.iterator()
        object : Iterator<T> {
            override fun hasNext(): Boolean {
                r.enter(cell)
                try {
                    return it.hasNext()
                } finally {
                    r.exit()
                }
            }

            override fun next(): T {
                r.enter(cell)
                try {
                    return it.next()
                } finally {
                    r.exit()
                }
            }
        }
    }
}

class Recording(val trace: Writer?) {
    val startNanos = System.nanoTime()

    /** Charged with whatever runs outside every phase. */
    private val none = Cell(-1, null)
    private val stack = ArrayList<Cell>().apply { add(none) }

    @Volatile
    var current: Cell = none
        private set

    @Volatile
    private var lastSwitch = startNanos

    private val queries = ArrayList<QueryStats>()
    private val events = ArrayList<Map<String, Any?>>()
    val info: MutableMap<String, Any?> = java.util.Collections.synchronizedMap(LinkedHashMap())

    fun cell(query: Int, phase: Phase): Cell =
        if (query < 0) none else synchronized(queries) { queries[query] }.cells[phase.ordinal]

    fun enter(cell: Cell) {
        val now = System.nanoTime()
        current.nanos += now - lastSwitch
        lastSwitch = now
        stack.add(cell)
        current = cell
    }

    fun exit() {
        val now = System.nanoTime()
        current.nanos += now - lastSwitch
        lastSwitch = now
        stack.removeAt(stack.size - 1)
        current = stack.last()
    }

    fun newQuery(round: Int, outerDepth: Int, names: List<String>, numPos: Int, numNeg: Int): Int =
        synchronized(queries) {
            queries.add(QueryStats(queries.size, round, outerDepth, names, numPos, numNeg))
            queries.size - 1
        }

    fun event(kind: String, fields: Map<String, Any?>) {
        val e = LinkedHashMap<String, Any?>()
        e["ms"] = millisSince(startNanos)
        e["kind"] = kind
        current.let { if (it.query >= 0) e["query"] = it.query }
        e.putAll(fields)
        synchronized(events) { events.add(e) }
    }

    @Synchronized
    fun writeTrace(kind: String, state: Any) {
        val c = current
        trace!!.write(
            Json.write(
                mapOf(
                    "query" to c.query,
                    "phase" to c.phase?.key,
                    "kind" to kind,
                    "state" to state.toString()
                )
            )
        )
        trace.write("\n")
    }

    /**
     * Everything recorded so far, as JSON-ready maps. Safe to call from another thread while the
     * search runs, as a timeout does; the phase running then is charged up to now.
     */
    fun snapshot(): Map<String, Any?> {
        val now = System.nanoTime()
        val running = current
        val runningExtra = now - lastSwitch
        fun nanos(c: Cell) = c.nanos + if (c === running) runningExtra else 0L

        val qs = synchronized(queries) { queries.toList() }
        val totalCounts = LongArray(Count.values().size)
        val phaseNanos = LongArray(Phase.values().size)
        val phaseCounts = Array(Phase.values().size) { LongArray(Count.values().size) }

        fun countsOf(c: Cell) = LongArray(Count.values().size) { c.counts[it] }

        fun countsJson(counts: LongArray, keepZeros: Boolean) =
            LinkedHashMap<String, Any?>().apply {
                Count.values().forEach {
                    val n = counts[it.ordinal]
                    if (keepZeros || n != 0L) put(it.key, if (it.nanos) n / 1_000_000.0 else n)
                }
            }

        fun cellJson(nanos: Long, counts: LongArray) =
            linkedMapOf<String, Any?>("ms" to nanos / 1_000_000.0) + countsJson(counts, keepZeros = false)

        val queriesJson =
            qs.map { q ->
                var queryNanos = 0L
                val phases = LinkedHashMap<String, Any?>()
                q.cells.forEach { c ->
                    val phase = c.phase!!
                    val n = nanos(c)
                    val counts = countsOf(c)
                    queryNanos += n
                    phaseNanos[phase.ordinal] += n
                    counts.forEachIndexed { i, v ->
                        totalCounts[i] += v
                        phaseCounts[phase.ordinal][i] += v
                    }
                    if (n != 0L || counts.any { it != 0L })
                        phases[phase.key] = cellJson(n, counts)
                }
                linkedMapOf(
                    "id" to q.id,
                    "round" to q.round,
                    "outerDepth" to q.outerDepth,
                    "names" to q.names,
                    "numPos" to q.numPos,
                    "numNeg" to q.numNeg,
                    "ms" to queryNanos / 1_000_000.0,
                    "phases" to phases,
                )
            }
        countsOf(none).forEachIndexed { i, v -> totalCounts[i] += v }

        return linkedMapOf(
            "wallMs" to (now - startNanos) / 1_000_000.0,
            "unattributedMs" to nanos(none) / 1_000_000.0,
            "counters" to countsJson(totalCounts, keepZeros = true),
            "phases" to
                Phase.values().associate { it.key to cellJson(phaseNanos[it.ordinal], phaseCounts[it.ordinal]) },
            "info" to synchronized(info) { LinkedHashMap(info) },
            "queries" to queriesJson,
            "events" to synchronized(events) { events.toList() },
        )
    }
}

private fun millisSince(startNanos: Long) = (System.nanoTime() - startNanos) / 1_000_000.0

/** Prints what the search is doing, for debugging by hand. Builds no strings unless enabled. */
object Debug {
    @JvmStatic
    var enabled = System.getProperty("typesynth.debug") != null

    inline fun log(message: () -> String) {
        if (enabled) println(message())
    }
}
