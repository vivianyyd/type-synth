package util

import runCommand
import java.io.File

private fun join(vararg dirs: String) = dirs.joinToString(separator = File.separator)
private val sharedPath = join("src", "main", "sketch", "symbolicgen", "generated")
private fun path(dir: String, testName: String) = join(sharedPath, dir, "$testName.sk")
private fun inputPath(testName: String) = path("input", testName)
private fun outputPath(testName: String) = path("output", testName)

private fun write(path: String, contents: String) = File(path).printWriter().use { it.println(contents) }

fun callSketch(input: String, testName: String): String {
    write(inputPath(testName), input)
    val out = "sketch ${inputPath(testName)} --slv-parallel --slv-nativeints --bnd-inline-amnt 5".runCommand()
        ?: throw Exception("I'm sad")
    write(outputPath(testName), out)
    return out
}

fun readOutput(testName: String) = File(outputPath(testName)).readText()
