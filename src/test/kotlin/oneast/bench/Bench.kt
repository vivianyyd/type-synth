package oneast.bench

/**
 * Parameters for the benchmarks in this package, read from `-Dbench.*` system properties.
 *
 * Gradle forks the test JVM and does not inherit `-D` from the daemon, so `build.gradle.kts`
 * forwards these explicitly — see the `forwarded` list in `tasks.test`. Add a prefix there
 * rather than registering a new task.
 *
 * Every benchmark is gated on [GATE] being set, so a plain `./gradlew test` never runs one:
 *
 *     ./gradlew test --tests "*EnumeratorBench*" -Dbench=1 -Dbench.limit=5000
 */
internal object Bench {
    /** Set `-Dbench=<anything>` to enable the benchmarks. */
    const val GATE = "bench"

    private fun raw(name: String): String? =
        System.getProperty("bench.$name")?.takeIf { it.isNotBlank() }

    fun str(name: String, default: String): String = raw(name) ?: default

    fun int(name: String, default: Int): Int =
        raw(name)?.let {
            it.toIntOrNull() ?: error("-Dbench.$name expects an integer, got \"$it\"")
        } ?: default

    fun list(name: String, default: List<String>): List<String> =
        raw(name)?.split(",")?.map { it.trim() }?.filter { it.isNotEmpty() } ?: default

    /** Present-or-absent flag: `-Dbench.dump` is on, however it is valued. */
    fun flag(name: String): Boolean = System.getProperty("bench.$name") != null
}
