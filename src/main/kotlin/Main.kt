import enumgen.DependencyAnalysis
import enumgen.Enumerator
import enumgen.EqualityOracle
import enumgen.NonArrowEnumerator
import enumgen.types.ArrowAnalysis
import enumgen.visualizations.DependencyGraphVisualizer
import util.*
import java.io.File
import java.io.IOException
import java.util.concurrent.TimeUnit


val exsWithSecretType = mapOf(
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
//    val t = "(->  a (-> (l a) (l a)) )"
//    val p = "(int)"
//    val lp = "(l (int))"
//    // make a test for list map
//    listOf(t, p, lp).map{
//        println(SExprParser(it).parse())
//        println(SExprParser(it).parse().toType())
//    }

//    val query = examples(exsWithSecretType.keys)
//    val oracle = ScrappyOracle(exsWithSecretType.mapKeys { parseApp(it.key) })
//    val da = DependencyAnalysis(query, oracle)
//    query.names.forEach { viz(it, da) }

    val query = examples(exsWithSecretType.keys)
    val consEnumerator = NonArrowEnumerator(
        query,
        ArrowAnalysis.unifyToTypes(query.posExamples.toList(), query.names, propagateEqualities = true)
    )
    consEnumerator.enumerate()
}

private fun viz(name: String, da: DependencyAnalysis) = DependencyGraphVisualizer.viz(da.graphs[name]!!, "$name")

/**
 * Requires [secretTypes[app]] is null iff [app] is a negative example
 */
class ScrappyOracle(private val secret: Map<Application, String?>) : EqualityOracle {
    override fun equal(a: Application, b: Application): Boolean =
        if (secret[a] == null || secret[b] == null) false else secret[a] == secret[b]
}

class PairwiseCheckOracle() : EqualityOracle {
    override fun equal(a: Application, b: Application): Boolean = TODO("memoize results")
}

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
