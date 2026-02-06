package util

import java.io.File
import java.io.IOException
import java.util.concurrent.TimeUnit

fun join(vararg dirs: String) = dirs.joinToString(separator = File.separator)

fun write(path: String, contents: String) = File(path).printWriter().use { it.println(contents) }

fun String.runCommand(workingDir: File = File(System.getProperty("user.dir"))): String? {
    return try {
        val parts = this.split("\\s".toRegex())
        val proc =
            ProcessBuilder(*parts.toTypedArray())
                .directory(workingDir)
                .redirectOutput(ProcessBuilder.Redirect.PIPE)
                .redirectError(ProcessBuilder.Redirect.PIPE)
                .start()

        proc.waitFor(60, TimeUnit.MINUTES)
        proc.inputStream.bufferedReader().readText()
    } catch (e: IOException) {
        e.printStackTrace()
        null
    }
}

fun deleteAll(path: String, and: (File) -> Boolean = { true }) {
    val directory = File(path)
    if (!directory.exists() || !directory.isDirectory) {
        return
    }
    directory.listFiles()?.forEach { file ->
        if (file.isFile && and(file)) {
            if (!file.delete()) {
                println("Failed to delete: ${file.name}")
            }
        }
    }
}
