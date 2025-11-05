import query.parseContextAndExamples
import test.*
import util.clearCVC
import util.clearOutlines
import util.readExamples
import java.io.File
import java.io.PrintStream

const val MAX_ITERATIONS = 2
const val REDO_ALL = false
const val WRITE_INTERMEDIATE = REDO_ALL
const val MAKE_OUTLINES = REDO_ALL
const val CALL_CVC = REDO_ALL

fun main() {
    val smallTests = listOf(IdTest, ConsTest, HOFTest, DictTest, WeirdTest)
    val smallTest = DictTest
    val testFromFile = parseContextAndExamples(readExamples("dictchain"))

    val (query, oracle) = (smallTest.query to smallTest.oracle)
//    val (query, oracle) = testFromFile
//    viz(query)

    val logFile = File("app.log")
    val logStream = PrintStream(logFile.outputStream(), true)
//    System.setOut(logStream)
//    System.setErr(logStream)

    if (MAKE_OUTLINES) clearOutlines()
    if (CALL_CVC) clearCVC()
    val TIME = System.currentTimeMillis()
    val OK = run(query, oracle)
    println("Solutions:")
    OK.forEach { println(it.toList().joinToString(separator = "\n", postfix = "\n---\n")) }
    println("${OK.size} satisfying contexts")
    println("TIME: ${System.currentTimeMillis() - TIME}")
}
