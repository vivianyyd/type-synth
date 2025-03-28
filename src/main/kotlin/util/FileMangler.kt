package util

import runCommand
import java.io.File

private fun join(vararg dirs: String) = dirs.joinToString(separator = File.separator)
private fun profilingResultPath(testName: String) = join("results", "$testName.csv")

// TODO can pass this in main function
private val customCodeGenerator = join("../applications/sketch-1.7.6/sketch-frontend/customcodegen.jar")
private val generationPath = join("src", "main", "sketch", "symbolicgen", "generated")

// TODO use --fe-inc so include statements don't have absolute paths
private fun path(dir: String, testName: String) = join(generationPath, dir, "$testName.sk")
private fun inputPath(testName: String) = path("input", testName)
private fun outputPath(testName: String) = path("output", testName)

private fun write(path: String, contents: String) = File(path).printWriter().use { it.println(contents) }

fun callSketch(input: String, testName: String): String {
    write(inputPath(testName), input)
    val flags = listOf(
        "--fe-custom-codegen $customCodeGenerator",
        "--slv-parallel",
        "-V 0",
        "--slv-nativeints",
        "--bnd-inline-amnt 5"
    ).joinToString(separator = " ")
    val out = "sketch ${inputPath(testName)} $flags".runCommand()
        ?: throw Exception("I'm sad")
    write(outputPath(testName), out)
    return out
}

fun readOutput(testName: String) = File(outputPath(testName)).readText()

fun writeProfiling(output: String, testName: String) = write(profilingResultPath(testName), output)
