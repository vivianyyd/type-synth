import enumgen.Enumerator
import enumgen.EqualityOracle
import enumgen.ExampleAnalysis
import util.SExprParser
import util.examplesSplit
import util.toExample
import util.Application
import util.print
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

//    testEnumeration()

    val exsexps = exsWithSecretType.mapKeys { SExprParser(it.key).parse() }
    val (pos, negs, names) = examplesSplit(exsexps.keys)
    val secretTypes = exsexps.mapKeys { it.key.toExample().second }
    val oracle = ScrappyOracle(secretTypes)
    println("Named values:\n$names")
    println("Positive examples:\n${pos.print(true)}")
    println("Negative examples:\n${negs.print(false)}")

    println(ExampleAnalysis(names.toList(), pos.toSet(), negs.toSet()).params)
}

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
    val (pos, negs, names) = examplesSplit(exsWithSecretType.keys.map { SExprParser(it).parse() })

    println("Posexs: \n${pos.print(true)}")
    println("Negexs: \n${negs.print(false)}")

    val consEnumerator = Enumerator(
        names = names.toList(),
        posExamples = pos.toSet(),
        negExamples = negs.toSet()
    )

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


    consEnumerator.enumerate()
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
