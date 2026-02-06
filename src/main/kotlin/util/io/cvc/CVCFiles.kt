package util.io.cvc

import util.*
import java.io.File

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

fun readInitialCVCresults(): List<Pair<Int, String>> =
    File(join("src", "main", "python", "output"))
        .listFiles()!!
        .filter { it.isFile && "smaller" !in it.name }
        .mapNotNull {
            if (it.isFile)
                it.name.substringAfter("cvc-").substringBeforeLast(".py").toInt() to it.readText()
            else null
        }
        .sortedBy { it.first }

fun readSmallestCVCresults(): List<Pair<Int, String>> {
    val initOutputs = readInitialCVCresults()
    val smallerOutputs =
        File(join("src", "main", "python", "output"))
            .listFiles()!!
            .filter { it.isFile && "smaller" in it.name }
            .eqClasses { f1, f2 ->
                f1.name.substringBeforeLast("-smaller") == f2.name.substringBeforeLast("-smaller")
            }
            .mapNotNull {
                val bestSoln =
                    it.maxByOrNull {
                        it.name.substringAfterLast("-smaller").substringBeforeLast(".py").toInt()
                    }!! // equivalenceClasses() guarantees nonemptiness of returned classes
                if (bestSoln.isFile)
                    bestSoln.name.substringAfter("cvc-").substringBeforeLast("-smaller").toInt() to
                            bestSoln.readText()
                else null
            }
            .sortedBy { it.first }
    return (smallerOutputs +
            initOutputs.filter { init ->
                smallerOutputs.none { smaller -> init.first == smaller.first }
            })
        .sortedBy { it.first }
}

fun readCVC(name: String): String? {
    val f = File(join("src", "main", "python", "output", "cvc-$name.py"))
    return if (f.isFile) f.readText() else null
}

fun clearCVC() {
    deleteAll(join("src", "main", "python", "output"))
    deleteAll(join("src", "main", "python", "input", "generated")) { it.name != "cardinality.py" }
}
