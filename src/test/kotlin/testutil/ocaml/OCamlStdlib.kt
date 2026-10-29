package testutil.ocaml

import oneast.SearchState
import oneast.Type
import query.Example
import query.Query
import testutil.splitOCamlExamples
import testutil.SExpr
import testutil.parseSExpr
import testutil.toExample
import util.CheckingGroundTruthOracle
import util.GroundTruth
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
        ?.forEach { file -> putAll(parseTypesFile(parser, file).mapValues { it.value.type }) }
})

/** Modules whose .types file has no `// Module` header line. */
private val moduleNameOverrides = mapOf("22_array_mod.types" to "Array", "24_bool_mod.types" to "Bool")

/** The module a module's file (`*_mod.types`) declares, from its `// Module` header line. */
private fun moduleOf(file: File): String? =
    if (!file.name.endsWith("_mod.types")) null
    else moduleNameOverrides[file.name]
        ?: file.useLines { it.first() }.removePrefix("//").trim().split(Regex("\\s+")).first()

/** `// type ('a, 'b) t = definition`: the parameters, the name and the definition, if any. */
private val typeDeclaration = Regex("""//\s*type\s+((?:[!+-]?'\w+|\([^)]*\))\s+)?([a-z_]\w*)\s*(?:=\s*(.*))?""")

/** A type constructor name, possibly qualified: `char`, `Seq.t`. */
private val typeConstructor = Regex("""(?:[A-Z]\w*\.)*[a-z_]\w*""")

/**
 * The types that the `// type` comments of [module]'s file declare, mapped to the type each one
 * is. A declaration that only renames a type, like `type t = char` or `type 'a t = 'a option =
 * None | Some of 'a`, is the type it renames. Any other, abstract (`type t`) or not (a record, a
 * variant, `private int`, `unit -> 'a node`), is a type of its own, named in full: `Hashtbl.t`.
 */
private fun declaredTypes(file: File, module: String): Map<String, String> =
    file.readLines().mapNotNull { typeDeclaration.matchEntire(it.trim()) }.associate { match ->
        val (params, name, definition) = match.destructured
        val manifest = definition.substringBefore("=").trim()
        val renamed = manifest.substringAfterLast(" ")
        fun normalize(params: String) = params.replace(Regex("[!+\\-\\s]"), "")
        val isRename =
            typeConstructor.matches(renamed) &&
                normalize(manifest.removeSuffix(renamed)) == normalize(params)
        name to if (isRename) renamed.removePrefix("Stdlib.") else "$module.$name"
    }

/**
 * [typeRenames] of each directory read so far. Finding them reads every file in the directory, and
 * [parseTypesFile] needs them for each file it parses.
 */
private val renamesByDir = mutableMapOf<File, Map<String, String>>()

/** For each module type in [dir] that renames a type, like `Char.t`, the type it renames. */
private fun typeRenames(dir: File): Map<String, String> =
    renamesByDir.getOrPut(dir.absoluteFile) {
        dir.listFiles()!!.flatMap { file ->
            val module = moduleOf(file) ?: return@flatMap emptyList()
            declaredTypes(file, module).map { (name, type) -> "$module.$name" to type }
        }.filter { (name, type) -> name != type }.toMap()
    }

/**
 * Parses a .types file. A module's file (`*_mod.types`) names its values relative to the module
 * (`create`, `Ascii.lowercase`), but examples use full names (`Mutex.create`,
 * `Char.Ascii.lowercase`), so this qualifies them. As in the examples, operators and constructors
 * stay unqualified, and names the file already qualifies (`List.length`) are kept.
 *
 * Type names are relative to the module too, and each module has its own `t`, so a type the module
 * declares, or one in a submodule of it (`DLS.key` in Domain), is named in full: `Domain.t`,
 * `Domain.DLS.key`. Then, in every file, a type that renames another, like `Char.t`, is the type it
 * renames, `char`.
 */
fun parseTypesFile(parser: OcamlTypeParser, file: File): Map<String, Signature> {
    val renames = typeRenames(file.parentFile)
    val module = moduleOf(file)
        ?: return parser.parseSignaturesWithLabels(file.readText()) { renames[it] ?: it }
    val declared = declaredTypes(file, module)
    val text = file.readText()
    // Only for the value names, to find the submodules. A parser records every type name it parses
    // (constructorNames), so [parser] would also record the names this pass doesn't rename, like `t`.
    val relativeNames = OcamlTypeParser().parseSignatures(text).keys.map { it.removePrefix("$module.") }
    val submodules = relativeNames.filter { '.' in it }.map { it.substringBefore('.') }.toSet()
    val signatures = parser.parseSignaturesWithLabels(text) { name ->
        when {
            name in declared -> declared.getValue(name)
            name.substringBefore('.', "") in submodules -> "$module.$name"
            else -> renames[name] ?: name
        }
    }
    return signatures.mapKeys { (name) ->
        val unqualified =
            name.startsWith("(") || name.startsWith("$module.") ||
                (name.first().isUpperCase() && '.' !in name)
        if (unqualified) name else "$module.$name"
    }
}

/**
 * How stdlib examples are written as OCaml: with the labels of every value the stdlib .types files
 * declare, and the instances of functors that examples use (see 51_map_mod.types). Names are
 * qualified, so no two modules' values share labels.
 */
val stdlibSource: OCamlSource by lazy {
    val parser = OcamlTypeParser()
    OCamlSource(
        labels = ocamlTypesDir.listFiles()!!.filter { it.extension == "types" }
            .flatMap { parseTypesFile(parser, it).entries }
            .associate { it.key to it.value.labels }
            .filterValues { labels -> labels.any { it != null } },
        prelude = "module StrMap = Map.Make (String)"
    )
}

/**
 * Loads examples and oracle types from a list of .exs files.
 * Each .exs file's first line must be a comment listing the .types files it depends on, e.g.:
 *   // 0_basics.types, 4_arith.types
 * All subsequent non-comment, non-blank lines are treated as examples. Examples cannot be lambdas or
 * lets yet, so of an example that has them, only the subexpressions outside them are kept.
 * Constructor ids come from [parser], so types loaded by separate calls share ids only if they share
 * the parser.
 */
fun loadFromExsFiles(
    exsFileNames: List<String>,
    parser: OcamlTypeParser = OcamlTypeParser()
): Pair<List<Example>, Map<String, Type>> {
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
                val example = parseSExpr(trimmed).withoutBinders().toExample()
                if (BINDER !in example.names) examples.add(example)
                else examples.addAll(example.subexprs().filter { BINDER !in it.names })
            }
        }
    }
    val oracleTypes = buildMap {
        referencedTypesFiles.forEach { typesFileName ->
            val typesFile = File(ocamlTypesDir, typesFileName)
            if (typesFile.isFile) putAll(parseTypesFile(parser, typesFile).mapValues { it.value.type })
        }
    }
    return examples to oracleTypes
}

/** The name [withoutBinders] gives a lambda or let, which no example can use. */
private const val BINDER = "<binder>"

/** [this] with each lambda, `(fun x -> body)`, and let, `(let x = value in body)`, made [BINDER]. */
private fun SExpr.withoutBinders(): SExpr =
    when (this) {
        is SExpr.Atm -> this
        is SExpr.Lst ->
            if ((elements.firstOrNull() as? SExpr.Atm)?.value in setOf("fun", "let")) SExpr.Atm(BINDER)
            else SExpr.Lst(elements.map { it.withoutBinders() })
    }

/**
 * The problem of finding types for the names in modules [task], given the true types of the names
 * that modules [fixed]'s examples use, along with the answer. Like a chain that solved [fixed] first,
 * names that no example of [fixed] uses aren't given, so they don't fix labels the task's names
 * use (`Option.to_list` would fix `list`'s). [committedSeed] replaces the true types of [fixed] as
 * what the search starts from. [groundTruth] splits the examples into positive and negative ones.
 */
fun ocamlModulesQuery(
    task: List<String>,
    fixed: List<String>,
    committedSeed: SearchState? = null,
    groundTruth: GroundTruth = OCamlGroundTruth.default.create(stdlibSource),
): Pair<Query, SearchState> {
    // One parser, so that a label id means the same constructor in both maps.
    val parser = OcamlTypeParser()
    val (fixedExamples, fixedTypes) = loadFromExsFiles(fixed, parser)
    val (examplesAll, desiredTypes) = loadFromExsFiles(task, parser)
    val given = fixedTypes.filterKeys { name -> fixedExamples.any { name in it.names } }
    val oracleTypes = fixedTypes + desiredTypes
    val examples =
        examplesAll
            .flatMap { it.subexprs() }
            .toSet()
            .filter { it.names.all { it in oracleTypes } }
    val oracle = CheckingGroundTruthOracle(oracleTypes)
    val query =
        Query(
            splitOCamlExamples(examples, oracle, groundTruth),
            oracle,
            committedSeed = committedSeed ?: stateFromContext(given)
        )
    return query to stateFromContext(oracleTypes)
}

/**
 * Modules solved together, from the examples in [files]. [deps] names the groups whose names
 * [files]' examples use.
 */
class OCamlModuleGroup(val name: String, val files: List<String>, val deps: List<String> = emptyList())

/** In the order the full chain solves them, each after its [OCamlModuleGroup.deps]. */
val ocamlModuleGroups: List<OCamlModuleGroup> =
    listOf(
        // Only constants, which every other group uses, and no examples
        OCamlModuleGroup("basics", listOf("0_basics")),
        OCamlModuleGroup("arith", listOf("4_arith"), deps = listOf("basics")),
        OCamlModuleGroup("boolean", listOf("2_boolean"), deps = listOf("arith")),
        OCamlModuleGroup("char", listOf("8_char"), deps = listOf("arith")),
        OCamlModuleGroup("comparison", listOf("1_comparison"), deps = listOf("basics")),
        OCamlModuleGroup("bitwise", listOf("5_bitwise"), deps = listOf("arith")),
        OCamlModuleGroup("str", listOf("7_str"), deps = listOf("basics")),
        OCamlModuleGroup("unit", listOf("9_unit"), deps = listOf("arith", "comparison", "str")),
        OCamlModuleGroup("pair_mod", listOf("76_pair_mod"), deps = listOf("boolean", "comparison", "unit")),
        OCamlModuleGroup("pair", listOf("11_pair"), deps = listOf("pair_mod")),
        OCamlModuleGroup("float", listOf("6_float"), deps = listOf("arith", "pair")),
        OCamlModuleGroup("bool_mod", listOf("24_bool_mod"), deps = listOf("boolean", "comparison", "float", "str")),
        OCamlModuleGroup("char_mod", listOf("28_char_mod"), deps = listOf("boolean", "char", "comparison", "str")),
        OCamlModuleGroup("unit_mod", listOf("74_unit_mod"), deps = listOf("boolean", "comparison", "unit")),
        OCamlModuleGroup("option_mod", listOf("57_option_mod"), deps = listOf("boolean", "comparison", "str", "unit")),
        OCamlModuleGroup("strconv", listOf("10_strconv"), deps = listOf("boolean", "comparison", "float", "option_mod")),
        OCamlModuleGroup(
            "list", listOf("50_list_mod"), deps = listOf("boolean", "char", "comparison", "option_mod", "pair", "unit")
        ),
        OCamlModuleGroup("queue_mod", listOf("62_queue_mod"), deps = listOf("list", "option_mod", "str", "unit")),
        OCamlModuleGroup("fun_mod", listOf("40_fun_mod"), deps = listOf("boolean", "comparison", "str", "unit")),
        OCamlModuleGroup(
            "string_mod", listOf("70_string_mod"), deps = listOf("char_mod", "fun_mod", "list", "option_mod", "str")
        ),
        OCamlModuleGroup("map_mod", listOf("51_map_mod"), deps = listOf("fun_mod", "list", "option_mod", "str")),
    )
        .also { groups ->
            groups.forEachIndexed { i, group ->
                val before = groups.subList(0, i).map { it.name }
                group.deps.forEach { require(it in before) { "${group.name} comes before its dependency $it" } }
            }
        }

fun ocamlModuleGroup(name: String): OCamlModuleGroup =
    ocamlModuleGroups.find { it.name == name } ?: error("No OCaml module group named $name")

/** [group] and the groups it depends on, directly or not, in [ocamlModuleGroups]' order. */
fun withDependencies(group: OCamlModuleGroup): List<OCamlModuleGroup> {
    val needed = mutableSetOf<String>()
    fun visit(name: String) {
        if (needed.add(name)) ocamlModuleGroup(name).deps.forEach(::visit)
    }
    visit(group.name)
    return ocamlModuleGroups.filter { it.name in needed }
}
