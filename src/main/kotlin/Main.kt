import bottomup.BottomUp
import sketchral.InputFactory
import sketchral.OutputParser
import sketchral.Result
import sketchral.withNegEx
import util.*
import java.io.File
import java.io.IOException
import java.util.concurrent.TimeUnit 
 
/*fun bottomUpTests() {
    val bu = BottomUp(listquery)
    println("Running bottom-up for MutableList.add")
    println("Found ${bu.enumerate(addFunc, 6)}")
    println("Running bottom-up for MutableList.addAll")
    println("Found ${bu.enumerate(addAllFunc, 6)}")
    println("Running bottom-up for duplicate")
    println("Found ${bu.enumerate(dupFunc, 6)}")
}*/

fun writeToTmp(content: String) = File("tmp.sk").printWriter().use { out -> out.println(content) }

fun callSketch(input: String): String {
    writeToTmp(input)
    return ("sketch tmp.sk -V 5 --slv-nativeints --bnd-inline-amnt 5".runCommand())
        ?: throw Exception("I'm sad")
}

//val tests = listOf(ListQuery(), ArithmeticQuery)
fun main(args: Array<String>) {
    listTest.runTest()
    arithmeticTest.runTest()
    stringTest.runTest()
}

fun String.runCommand( 
    workingDir: File = File(System.getProperty("user.dir"))
): String? {
    try {
        val parts = this.split("\\s".toRegex())
        val proc = ProcessBuilder(*parts.toTypedArray())
            .directory(workingDir)
            .redirectOutput(ProcessBuilder.Redirect.PIPE)
            .redirectError(ProcessBuilder.Redirect.PIPE)
            .start()

        proc.waitFor(60, TimeUnit.MINUTES)
        return proc.inputStream.bufferedReader().readText()
    } catch (e: IOException) {
        e.printStackTrace()
        return null
    }
}

