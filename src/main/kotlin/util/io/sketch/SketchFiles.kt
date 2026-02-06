package util.io.sketch

import util.join
import util.runCommand
import util.write
import java.io.File

// TODO can pass this in main function
private val customCodeGenerator =
    join("../applications/sketch-1.7.6/sketch-frontend/customcodegen.jar")

private fun sketchGenerationPath(task: String, inOrOutput: String, testName: String) =
    join("src", "main", "sketch", task, "generated", inOrOutput, "$testName.sk")

// TODO use --fe-inc so include statements don't have absolute paths
private fun skSymInput(testName: String) = sketchGenerationPath("symbolicgen", "input", testName)

private fun skSymOutput(testName: String) = sketchGenerationPath("symbolicgen", "output", testName)

fun callSketch(content: String, testName: String): String {
    write(skSymInput(testName), content)
    val flags =
        listOf(
            "--fe-custom-codegen $customCodeGenerator",
            "--slv-parallel",
            "-V 0",
            "--slv-nativeints",
            "--bnd-inline-amnt 3"
        )
            .joinToString(separator = " ")
    val out = "sketch ${skSymInput(testName)} $flags".runCommand() ?: throw Exception("I'm sad")
    write(skSymOutput(testName), out)
    return out
}

fun writeConcretizeInput(content: String, testName: String) =
    write(sketchGenerationPath("concretize", "input", testName), content)

fun readSymSketchOutput(testName: String) = File(skSymOutput(testName)).readText()
