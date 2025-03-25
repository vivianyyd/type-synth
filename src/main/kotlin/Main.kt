import enumgen.DependencyAnalysis
import enumgen.Enumerator
import enumgen.NonArrowEnumerator
import enumgen.types.ArrowAnalysis
import enumgen.types.Type
import enumgen.types.checkApplication
import enumgen.types.toType
import enumgen.visualizations.DependencyGraphVisualizer
import examplegen.ExampleGenerator
import util.*
import java.io.File
import java.io.IOException
import java.util.concurrent.TimeUnit


val consExamples = mapOf(
    "(+ 0)" to "int",
    "(+ tr)" to "bool",
    "(+ []i)" to "lint",
    "(+ []b)" to "lbool",
    "(+ [[]]i)" to "llint",
    "(+ (cons 0 []i))" to "lint",
    "(+ (cons 0 (cons 0 []i)))" to "lint",
    "(+ (cons tr []b))" to "lbool",
    "(+ (cons tr (cons tr []b)))" to "lbool",
    "(+ (cons []i [[]]i))" to "llint",
    "(+ (cons []i (cons []i [[]]i)))" to "llint",
    "(- (cons tr []i))" to null,
    "(- (cons []i 0))" to null,
    "(- (cons 0 []b))" to null,
    "(- (cons 0 [[]]i))" to null,
    "(- (cons tr [[]]i))" to null,
    "(- (cons tr (cons 0 []i)))" to null,
)//            Application("cons", listOf(emptyBoolList, emptyIntListList)),


fun main() {
//    // TODO make a test for list map
//    val query = parseExamples(consExamples.keys)
//    val oracle = ScrappyOracle(consExamples.mapKeys { parseApp(it.key) })
//    val da = DependencyAnalysis(query, oracle)
//    query.names.forEach { viz(it, da) }
//    val consEnumerator =
//        NonArrowEnumerator(
////        Enumerator(
//            query,
//        ArrowAnalysis.unifyToTypes(query.posExamples.toList(), query.names, propagateEqualities = true)
//        )
//    consEnumerator.enumerate()

//    val types = listOf("(i)", "(b)", "(-> a (-> (l a) (l a)))")
    val types = listOf("(i)", "(b)", "(-> a (-> (l b c) (-> (l a b) (l c))))")
    val (query, context) = ExampleGenerator(
        1,
        2,
        30,
        types.map { tySexpr -> SExprParser(tySexpr).parse().toType() },
    ).examples()
    val oracle = CheckingOracle(context)
    println(context)
    println(query.posExamples)
    val da = DependencyAnalysis(query, oracle)
    query.names.forEach { viz(it, da) }

}

private fun viz(name: String, da: DependencyAnalysis) = DependencyGraphVisualizer.viz(da.graphs[name]!!, "$name")

fun testEnumeration() {
//    val one = Application("1", null)
//    val emptyDict = Application("\\{\\}", null)
//    val putZero = Application("put", listOf(emptyDict, zero, tr))
//    val putZeroOne = Application("put", listOf(putZero, one, tr))
//    val putOne = Application("put", listOf(emptyDict, one, tr))
//
//    val dictEnumerator = Enumerator(
//        names = listOf("0", "1", "tr", "\\{\\}", "put"),
//        posExamples = setOf(
//            zero,
//            one,
//            tr,
//            emptyDict,
//            putZero,
//            putZeroOne,
//            putOne
//        ),
//        negExamples = setOf(
//            // TODO There are lots more which we can generate ourselves
//            Application("put", listOf(one, emptyDict, tr)),
//            Application("put", listOf(zero, zero, emptyDict))
//        )
//    )   // TODO Why does it think second argument can't be a literal?
//    dictEnumerator.enumerate()

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
