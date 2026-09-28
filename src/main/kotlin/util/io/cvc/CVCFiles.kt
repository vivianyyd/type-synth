package util.io.cvc

import bench.Count
import bench.Stats
import util.*
import java.io.File
import java.nio.file.Files

/**
 * Where solver queries and answers go. Each process gets a directory of its own, so that runs at
 * the same time cannot read or delete each other's files. Set the system property typesynth.cvcDir
 * to keep them somewhere to look at.
 */
private val cvcDir: File by lazy {
    System.getProperty("typesynth.cvcDir")?.let { File(it) }
        ?: Files.createTempDirectory("type-synth-cvc").toFile().also { dir ->
            Runtime.getRuntime().addShutdownHook(Thread { dir.deleteRecursively() })
        }
}
private val inputDir by lazy { File(cvcDir, "input").apply { mkdirs() } }
private val outputDir by lazy { File(cvcDir, "output").apply { mkdirs() } }

fun callCVC(content: String, testName: String): Boolean {
    val start = System.nanoTime()
    val inPath = File(inputDir, "cvc-$testName.py").path
    val outPath = File(outputDir, "cvc-$testName.py").path
    write(inPath, content)
    // cardinality.py lives in src/main/python/input, not alongside the generated files
    val out = "env PYTHONPATH=${join("src", "main", "python", "input")} python3 $inPath".runCommand()
        ?: throw Exception("I'm sad")
    Stats.inc(Count.SOLVER_CALLS)
    Stats.add(Count.SOLVER_NANOS, System.nanoTime() - start)
    if ("no solution" !in out) {
        write(outPath, out)
        return true
    }
    return false
}

fun readInitialCVCresults(): List<Pair<Int, String>> =
    outputDir
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
        outputDir
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
    val f = File(outputDir, "cvc-$name.py")
    return if (f.isFile) f.readText() else null
}

fun clearCVC() {
    deleteAll(outputDir.path)
    deleteAll(inputDir.path)
}
