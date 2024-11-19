package enumgen

import java.io.FileOutputStream
import java.io.PrintWriter

fun main() {
    val zero = Application("0", null)
    val cons = Application("cons", null)
    val t = Application("t", null)
    val emptyIntList = Application("l[i]", null)
    val emptyBoolList = Application("l[b]", null)
    val emptyIntListList = Application("l[[i]]", null)

    val cons0empty = Application("cons", listOf(zero, emptyIntList, emptyIntList))
    val consTempty = Application("cons", listOf(t, emptyBoolList, emptyBoolList))
    val consListList = Application("cons", listOf(emptyIntList, emptyIntListList, emptyIntListList))

    val e = Enumerator(
        names = listOf("0", "cons", "t", "l[i]", "l[b]", "l[[i]]"),
        posExamples = setOf(
            zero,
            cons,
            t,
            emptyIntList,
            emptyBoolList,
            emptyIntListList,
            cons0empty,
            consTempty,
            consListList
        ),
        negExamples = setOf(Application("cons", listOf(t))),
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
