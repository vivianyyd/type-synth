package util

import runCommand
import java.io.File

private fun join(vararg dirs: String) = dirs.joinToString(separator = File.separator)
private fun profilingResultPath(testName: String) = join("results", "$testName.csv")

// TODO can pass this in main function
private val customCodeGenerator = join("../applications/sketch-1.7.6/sketch-frontend/customcodegen.jar")
private val sketchGenerationPath = join("src", "main", "sketch", "symbolicgen", "generated")

// TODO use --fe-inc so include statements don't have absolute paths
private fun sketchPath(dir: String, testName: String) = join(sketchGenerationPath, dir, "$testName.sk")
private fun sketchInputPath(testName: String) = sketchPath("input", testName)
private fun sketchOutputPath(testName: String) = sketchPath("output", testName)
private fun write(path: String, contents: String) = File(path).printWriter().use { it.println(contents) }

fun callSketch(input: String, testName: String): String {
    write(sketchInputPath(testName), input)
    val flags = listOf(
        "--fe-custom-codegen $customCodeGenerator",
        "--slv-parallel",
        "-V 0",
        "--slv-nativeints",
        "--bnd-inline-amnt 5"
    ).joinToString(separator = " ")
    val out = "sketch ${sketchInputPath(testName)} $flags".runCommand()
        ?: throw Exception("I'm sad")
    write(sketchOutputPath(testName), out)
    return out
}

fun readSketchOutput(testName: String) = File(sketchOutputPath(testName)).readText()

fun writeProfiling(output: String, testName: String) = write(profilingResultPath(testName), output)
