import util.*
import java.io.File
import java.io.IOException
import java.util.concurrent.TimeUnit

fun writeToTmp(content: String) = File("tmp.sk").printWriter().use { out -> out.println(content) }

fun callSketch(input: String): String {
    writeToTmp(input)
    return ("sketch tmp.sk -V 5 --slv-nativeints --bnd-inline-amnt 5".runCommand())
        ?: throw Exception("I'm sad")
}

//val tests = listOf(ListQuery(), ArithmeticQuery)
fun main(args: Array<String>) {
    val initialConstraints = listOf(
        // we can get these by propagating equalities, still nontrivial
        Equality(
            TypeApplication("cons", listOf(Parameter(0), Parameter(1))),
            Parameter(2)
        ),
        Equality(
            TypeApplication("cons", listOf(UnknownType("t1"), UnknownType("t2"))),
            UnknownType("t2")
        ),
        Equality(
            TypeApplication("cons", listOf(UnknownType("t2"), UnknownType("t3"))),
            UnknownType("t3")
        ),
        Equality(
            TypeApplication("cons", listOf(LiteralTree(LiteralLabel("int"), listOf()), UnknownType("t2"))),
            UnknownType("t2")
        ),
    )
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

