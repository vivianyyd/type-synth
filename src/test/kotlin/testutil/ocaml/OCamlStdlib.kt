package testutil.ocaml

import oneast.SearchState
import oneast.Type
import query.Example
import query.Query
import testutil.splitOCamlExamples
import testutil.unsignedExample
import util.CheckingGroundTruthOracle
import util.join
import util.stateFromContext
import java.io.File

private val stdlibDir = join("src", "test", "input", "ocaml-stdlib")
val ocamlExsDir = File(join(stdlibDir, "exs"))
val ocamlTypesDir = File(join(stdlibDir, "types"))

fun oracleFromDir(dir: File) = CheckingGroundTruthOracle(buildMap {
    val parser = OcamlTypeParser()
    dir.listFiles()
        ?.filter { it.extension == "types" && it.isFile }
        ?.forEach { file -> putAll(parser.parseSignatures(file.readText())) }
})

/**
 * Loads examples and oracle types from a list of .exs files.
 * Each .exs file's first line must be a comment listing the .types files it depends on, e.g.:
 *   // 0_basics.types, 4_arith.types
 * All subsequent non-comment, non-blank lines are treated as examples.
 */
fun loadFromExsFiles(exsFileNames: List<String>): Pair<List<Example>, Map<String, Type>> {
    val examples = mutableListOf<Example>()
    val referencedTypesFiles = linkedSetOf<String>()

    for (name in exsFileNames) {
        val file = File(ocamlExsDir, if (name.endsWith(".exs")) name else "$name.exs")
        val lines = file.readLines()
        if (lines.isEmpty()) continue
        val firstLine = lines[0].trim()
        if (firstLine.startsWith("//")) {
            firstLine.removePrefix("//").trim()
                .split(",")
                .map { it.trim() }
                .filter { it.endsWith(".types") }
                .forEach {
                    if (it.substringBefore(".types") !in exsFileNames)
                        println("Warning in module $name: Dependency $it is not in provided files, adding its type signatures without its examples")
                    referencedTypesFiles.add(it)
                }
        }
        lines.drop(1).forEach { line ->
            val trimmed = line.trim()
            if (trimmed.isNotBlank() && !trimmed.startsWith("//")) {
                examples.add(unsignedExample(trimmed))
            }
        }
    }
    val parser = OcamlTypeParser()
    val oracleTypes = buildMap {
        referencedTypesFiles.forEach { typesFileName ->
            val typesFile = File(ocamlTypesDir, typesFileName)
            if (typesFile.isFile) putAll(parser.parseSignatures(typesFile.readText()))
        }
    }
    return examples to oracleTypes
}

/**
 * The problem of finding types for the names in modules [task], given the true types of the names
 * in modules [fixed], along with the answer.
 */
fun ocamlModulesQuery(task: List<String>, fixed: List<String>): Pair<Query, SearchState> {
    val (_, fixedTypes) = loadFromExsFiles(fixed)
    val (examplesAll, desiredTypes) = loadFromExsFiles(task)
    val oracleTypes = fixedTypes + desiredTypes
    val examples =
        examplesAll
            .flatMap { it.subexprs() }
            .toSet()
            .filter { it.names.all { it in oracleTypes } }
    val oracle = CheckingGroundTruthOracle(oracleTypes)
    val query =
        Query(
            splitOCamlExamples(examples, oracle, OCamlChecker()),
            oracle,
            committedSeed = stateFromContext(fixedTypes)
        )
    return query to stateFromContext(oracleTypes)
}

/** Groups of modules to solve in order, each given the true types of the groups before it. */
val ocamlModuleGroups =
    listOf(
        listOf("0_basics", "2_boolean", "4_arith", "8_char"),
        listOf("1_comparison"),
        listOf("50_list_mod"),
        listOf("5_bitwise"),
        listOf("6_float"),
        listOf("7_str"),
    )
