package util

import java.io.File
import java.io.IOException
import java.util.concurrent.TimeUnit

private fun join(vararg dirs: String) = dirs.joinToString(separator = File.separator)
private fun profilingResultPath(testName: String) = join("results", "$testName.csv")

// TODO can pass this in main function
private val customCodeGenerator = join("../applications/sketch-1.7.6/sketch-frontend/customcodegen.jar")
private fun sketchGenerationPath(task: String, inOrOutput: String, testName: String) =
    join("src", "main", "sketch", task, "generated", inOrOutput, "$testName.sk")

// TODO use --fe-inc so include statements don't have absolute paths
private fun skSymInput(testName: String) = sketchGenerationPath("symbolicgen", "input", testName)
private fun skSymOutput(testName: String) = sketchGenerationPath("symbolicgen", "output", testName)
private fun write(path: String, contents: String) = File(path).printWriter().use { it.println(contents) }

fun writeConcretizeInput(content: String, testName: String) =
    write(sketchGenerationPath("concretize", "input", testName), content)

fun callSketch(content: String, testName: String): String {
    write(skSymInput(testName), content)
    val flags = listOf(
        "--fe-custom-codegen $customCodeGenerator",
        "--slv-parallel",
        "-V 0",
        "--slv-nativeints",
        "--bnd-inline-amnt 3"
    ).joinToString(separator = " ")
    val out = "sketch ${skSymInput(testName)} $flags".runCommand()
        ?: throw Exception("I'm sad")
    write(skSymOutput(testName), out)
    return out
}

fun readSymSketchOutput(testName: String) = File(skSymOutput(testName)).readText()

fun writeProfiling(output: String, testName: String) = write(profilingResultPath(testName), output)

fun String.runCommand(
    workingDir: File = File(System.getProperty("user.dir"))
): String? {
    return try {
        val parts = this.split("\\s".toRegex())
        val proc = ProcessBuilder(*parts.toTypedArray())
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
