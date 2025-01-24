package enumgen

import java.io.File
import java.io.IOException
import java.util.concurrent.TimeUnit

fun main() {
    val t = "(->  a (-> (l a) (l a)) )"
    val p = "(int)"
    val lp = "(l (int))"

    // make a test for list map

    listOf(t, p, lp).map{
        println(SExprParser(it).parse().toType())
    }
}

fun testEnumeration(){
    val zero = Application("0", null)
    val cons = Application("cons", null)
    val tr = Application("tr", null)
    val emptyIntList = Application("[]i", null)
    val emptyBoolList = Application("[]b", null)
    val emptyIntListList = Application("[[]]i", null)

    val cons0empty = Application("cons", listOf(zero, emptyIntList))
    val consTempty = Application("cons", listOf(tr, emptyBoolList))
    val consListList = Application("cons", listOf(emptyIntList, emptyIntListList))

    val consEnumerator = Enumerator(
        names = listOf("0", "cons", "tr", "[]i", "[]b", "[[]]i"),
        posExamples = setOf(
            zero,
            cons,
            tr,
            emptyIntList,
            emptyBoolList,
            emptyIntListList,
            cons0empty,
            consTempty,
            consListList
        ),
        negExamples = setOf(
            // TODO There are lots more which we can generate ourselves
            Application("cons", listOf(tr, emptyIntList)),
            Application("cons", listOf(emptyIntList, zero)),
            Application("cons", listOf(zero, emptyBoolList)),
            Application("cons", listOf(tr, emptyIntListList)),
            Application("cons", listOf(zero, emptyIntListList))
        ),
        0
    )



    val one = Application("1", null)
    val emptyDict = Application("\\{\\}", null)
    val putZero = Application("put", listOf(emptyDict, zero, tr))
    val putZeroOne = Application("put", listOf(putZero, one, tr))
    val putOne = Application("put", listOf(emptyDict, one, tr))

    val dictEnumerator = Enumerator(
        names = listOf("0", "1", "tr", "\\{\\}", "put"),
        posExamples = setOf(
            zero,
            one,
            tr,
            emptyDict,
            putZero,
            putZeroOne,
            putOne
        ),
        negExamples = setOf(
            // TODO There are lots more which we can generate ourselves
            Application("put", listOf(one, emptyDict, tr)),
            Application("put", listOf(zero, zero, emptyDict))
        ),
        0
    )   // TODO Why does it think second argument can't be a literal?


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
