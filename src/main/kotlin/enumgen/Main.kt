package enumgen

import java.io.FileOutputStream
import java.io.PrintWriter

fun main() {
    val zero = Application("0", null)
    val cons = Application("cons", null)
    val tr = Application("tr", null)
    val emptyIntList = Application("[]i", null)
    val emptyBoolList = Application("[]b", null)
    val emptyIntListList = Application("[[]]i", null)

    val cons0empty = Application("cons", listOf(zero, emptyIntList))
    val consTempty = Application("cons", listOf(tr, emptyBoolList))
    val consListList = Application("cons", listOf(emptyIntList, emptyIntListList))

    val e = Enumerator(
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
    println("result: ${e.enumerate()}")
    writeDotOutput(e.visualization)
}

fun writeDotOutput(contents: String) {
    val out = PrintWriter(FileOutputStream("type.dot"))
    out.println(contents)
    out.close()
}
