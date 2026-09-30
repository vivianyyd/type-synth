package util.io.cvc

import bench.Count
import bench.Stats
import util.*
import java.io.File
import java.nio.file.Files

/**
 * Where solver queries and answers go: a new directory per process, deleted at exit. Files are
 * named by state id, which restarts every process, so a directory used before could hand this run
 * another run's answers. Set the system property typesynth.cvcDir to put the directory in there
 * and keep it.
 */
private val cvcDir: File by lazy {
    val keepIn = System.getProperty("typesynth.cvcDir")
    if (keepIn != null) {
        File(keepIn).mkdirs()
        Files.createTempDirectory(File(keepIn).toPath(), "run-").toFile()
    } else {
        Files.createTempDirectory("type-synth-cvc").toFile().also { dir ->
            Runtime.getRuntime().addShutdownHook(Thread { dir.deleteRecursively() })
        }
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

fun readCVC(name: String): String? {
    val f = File(outputDir, "cvc-$name.py")
    return if (f.isFile) f.readText() else null
}
