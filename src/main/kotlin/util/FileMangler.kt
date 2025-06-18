package util

import stc.outline
import java.io.File
import java.io.IOException
import java.util.concurrent.TimeUnit

private fun join(vararg dirs: String) = dirs.joinToString(separator = File.separator)
private fun profilingResultPath(testName: String) = join("results", "$testName.csv")
private fun write(path: String, contents: String) = File(path).printWriter().use { it.println(contents) }

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

fun callCVC(content: String, testName: String): Boolean {
    val inPath = join("src", "main", "python", "input", "generated", "cvc-$testName.py")
    val outPath = join("src", "main", "python", "output", "cvc-$testName.py")
    write(inPath, content)
    val out = "python3 $inPath".runCommand() ?: throw Exception("I'm sad")
    if ("no solution" !in out) {
        write(outPath, out)
        return true
    }
    return false
}

fun readCVCresults(): List<Pair<Int, String>> =
    File(join("src", "main", "python", "output")).listFiles()!!.filter { it.isFile && "smaller" !in it.name }
        .mapNotNull {
            if (it.isFile) it.name.substringAfter("cvc-").substringBeforeLast(".py").toInt() to it.readText()
            else null
        }.sortedBy { it.first }

fun readCVC(name: String): String = File(join("src", "main", "python", "output", "cvc-$name.py")).readText()

fun writeProfiling(output: String, testName: String) = write(profilingResultPath(testName), output)

private fun generatedTestPath(name: String) = join("src", "test", "generated", "$name.sexp")

fun writeExamples(contents: String, name: String) =
    write(generatedTestPath(name), contents)

fun readExamples(name: String): Pair<String, List<String>> {
    val lines = File(generatedTestPath(name)).readText().split('\n')
    return lines.first() to lines.drop(1)
}

private fun intermediateOutlinePath(name: String) = join("results", "intermediate", "outline", "outline-$name.sexp")

fun writeIntermediateOutline(contents: String, name: String) = write(intermediateOutlinePath(name), contents)
fun readIntermediateOutlines() =
    File(join("results", "intermediate", "outline")).listFiles()!!.filter { it.isFile }
        .mapNotNull { file ->
            if (file.isFile) file.name.substringAfter("outline-").substringBeforeLast(".sexp")
                .toInt() to outline(file.readText()) else null
        }.sortedBy { it.first }

// TODO can pass this in main function
private val customCodeGenerator = join("../applications/sketch-1.7.6/sketch-frontend/customcodegen.jar")
private fun sketchGenerationPath(task: String, inOrOutput: String, testName: String) =
    join("src", "main", "sketch", task, "generated", inOrOutput, "$testName.sk")

// TODO use --fe-inc so include statements don't have absolute paths
private fun skSymInput(testName: String) = sketchGenerationPath("symbolicgen", "input", testName)
private fun skSymOutput(testName: String) = sketchGenerationPath("symbolicgen", "output", testName)

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

fun writeConcretizeInput(content: String, testName: String) =
    write(sketchGenerationPath("concretize", "input", testName), content)

fun readSymSketchOutput(testName: String) = File(skSymOutput(testName)).readText()
