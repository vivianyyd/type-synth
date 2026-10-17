package util

import java.io.File
import java.io.IOException
import java.util.concurrent.TimeUnit

fun join(vararg dirs: String) = dirs.joinToString(separator = File.separator)

fun write(path: String, contents: String) = File(path).printWriter().use { it.println(contents) }

/** Stdout of this command. With [checkExit], a nonzero exit status throws with the command's stderr. */
fun String.runCommand(
    workingDir: File = File(System.getProperty("user.dir")),
    checkExit: Boolean = false
): String? {
    return try {
        val parts = this.split("\\s".toRegex())
        val proc =
            ProcessBuilder(*parts.toTypedArray())
                .directory(workingDir)
                .redirectOutput(ProcessBuilder.Redirect.PIPE)
                .redirectError(ProcessBuilder.Redirect.PIPE)
                .start()

        proc.waitFor(60, TimeUnit.MINUTES)
        if (checkExit && proc.exitValue() != 0) {
            throw IllegalStateException(
                "`$this` exited with ${proc.exitValue()}:\n${proc.errorStream.bufferedReader().readText()}"
            )
        }
        proc.inputStream.bufferedReader().readText()
    } catch (e: IOException) {
        e.printStackTrace()
        null
    }
}
