package bench

import java.io.File
import java.net.InetAddress

/** The paths whose changes change what is benchmarked. */
private val codePaths = listOf("src", "build.gradle.kts", "settings.gradle.kts")

/** [anyExit] because some commands, like diff --no-index, fail when they find something. */
private fun git(vararg args: String, anyExit: Boolean = false): String {
    val proc = ProcessBuilder("git", *args).start()
    val out = proc.inputStream.bufferedReader().readText()
    return if (proc.waitFor() == 0 || anyExit) out.trim() else ""
}

class GitInfo(val commit: String, val branch: String, val subject: String, val patch: String) {
    val dirty get() = patch.isNotEmpty()
    val short get() = commit.take(8)

    fun toJson(patchFile: String?): Map<String, Any?> =
        linkedMapOf(
            "commit" to commit,
            "branch" to branch,
            "subject" to subject,
            "dirty" to dirty,
            "patch" to patchFile,
        )

    companion object {
        /** Includes changes to the code that are not committed, whether or not git tracks them. */
        fun read(): GitInfo {
            val untracked =
                git("ls-files", "--others", "--exclude-standard", "--", *codePaths.toTypedArray())
                    .lines()
                    .filter { it.isNotBlank() }
            val patch =
                (listOf(git("diff", "HEAD", "--", *codePaths.toTypedArray())) +
                    untracked.map { git("diff", "--no-index", "/dev/null", it, anyExit = true) })
                    .filter { it.isNotBlank() }
                    .joinToString("\n")
            return GitInfo(
                commit = git("rev-parse", "HEAD"),
                branch = git("rev-parse", "--abbrev-ref", "HEAD"),
                subject = git("log", "-1", "--format=%s"),
                patch = patch,
            )
        }
    }
}

fun machineJson(childJvmArgs: List<String>): Map<String, Any?> =
    linkedMapOf(
        "host" to runCatching { InetAddress.getLocalHost().hostName }.getOrNull(),
        "os" to "${System.getProperty("os.name")} ${System.getProperty("os.version")}",
        "cores" to Runtime.getRuntime().availableProcessors(),
        "jvm" to "${System.getProperty("java.vm.name")} ${System.getProperty("java.version")}",
        "jvmArgs" to childJvmArgs,
    )

fun javaExecutable(): String =
    File(File(System.getProperty("java.home"), "bin"), "java").path
