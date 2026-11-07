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
 * declare, the instances of functors that examples use (see 51_map_mod.types), and Triple (see
 * 79_triple_mod.types). Names are qualified, so no two modules' values share labels.
 */
val stdlibSource: OCamlSource by lazy {
    val parser = OcamlTypeParser()
    OCamlSource(
        labels = ocamlTypesDir.listFiles()!!.filter { it.extension == "types" }
            .flatMap { parseTypesFile(parser, it).entries }
            .associate { it.key to it.value.labels }
            .filterValues { labels -> labels.any { it != null } },
        prelude = "module StrMap = Map.Make (String) " +
            "module Triple = struct let make a b c = (a, b, c) let fst (a, _, _) = a let snd (_, b, _) = b " +
            "let thd (_, _, c) = c end"
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
 * what the search starts from. Examples that need the search to solve one of [skippedNames] are left
 * out. [groundTruth] splits the examples into positive and negative ones.
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
    val seed = committedSeed ?: stateFromContext(given)
    val oracleTypes = fixedTypes + desiredTypes
    val examples =
        examplesAll
            .flatMap { it.subexprs() }
            .toSet()
            .filter { it.names.all { it in oracleTypes } }
            .filter { it.names.none { it in skippedNames && it !in seed.names } }
    val oracle = CheckingGroundTruthOracle(oracleTypes)
    val query = Query(splitOCamlExamples(examples, oracle, groundTruth), oracle, committedSeed = seed)
    return query to stateFromContext(oracleTypes)
}

/**
 * Names the search doesn't solve for now: examples that use one are left out, unless the search starts
 * with its type. `List.to_seq` gets a Seq label with no parameter, and a later round can't give the
 * label one, so `List.of_seq` has no solution.
 */
val skippedNames = setOf("List.to_seq", "List.of_seq")

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
        OCamlModuleGroup("comparison", listOf("1_comparison"), deps = listOf("basics")),
        // Its examples use `true` and `false` without anything tying them, so `comparison`, whose
        // examples do (`((=) true false)`), gives them their type. `boolean` can't: it uses arith's names.
        OCamlModuleGroup("arith", listOf("4_arith"), deps = listOf("basics", "comparison")),
        OCamlModuleGroup("boolean", listOf("2_boolean"), deps = listOf("arith")),
        OCamlModuleGroup("char", listOf("8_char"), deps = listOf("arith")),
        OCamlModuleGroup("bitwise", listOf("5_bitwise"), deps = listOf("arith")),
        OCamlModuleGroup("str", listOf("7_str"), deps = listOf("basics")),
        OCamlModuleGroup("unit", listOf("9_unit"), deps = listOf("arith", "comparison", "str")),
        OCamlModuleGroup("pair_mod", listOf("76_pair_mod"), deps = listOf("boolean", "comparison", "unit")),
        OCamlModuleGroup("pair", listOf("11_pair"), deps = listOf("pair_mod")),
        OCamlModuleGroup("triple_mod", listOf("79_triple_mod"), deps = listOf("boolean", "comparison", "unit")),
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
        OCamlModuleGroup(
            "map_mod", listOf("51_map_mod"), deps = listOf("fun_mod", "list", "option_mod", "str", "triple_mod")
        ),
        OCamlModuleGroup(
            "composition", listOf("3_composition"), deps = listOf("arith", "boolean", "comparison", "float", "strconv")
        ),
        OCamlModuleGroup("ref", listOf("19_ref"), deps = listOf("arith", "comparison", "unit")),
        OCamlModuleGroup("int_mod", listOf("45_int_mod"), deps = listOf("arith", "boolean", "comparison", "float", "str")),
        OCamlModuleGroup(
            "stdout",
            listOf("14_stdout"),
            deps = listOf("boolean", "char", "comparison", "float", "option_mod", "str", "string_mod", "unit")
        ),
        OCamlModuleGroup("stack_mod", listOf("69_stack_mod"), deps = listOf("list", "option_mod", "stdout", "str", "unit")),
        OCamlModuleGroup(
            "hashtbl_mod", listOf("42_hashtbl_mod"), deps = listOf("fun_mod", "list", "option_mod", "str", "unit")
        ),
        OCamlModuleGroup(
            "either_mod",
            listOf("35_either_mod"),
            deps = listOf("boolean", "comparison", "option_mod", "str", "strconv", "unit")
        ),
        OCamlModuleGroup(
            "result_mod",
            listOf("64_result_mod"),
            deps = listOf(
                "boolean", "comparison", "list", "option_mod", "pair_mod", "queue_mod", "stdout", "str", "strconv", "unit"
            )
        ),
        OCamlModuleGroup(
            "int32_mod",
            listOf("46_int32_mod"),
            deps = listOf("arith", "boolean", "comparison", "float", "option_mod", "str")
        ),
        OCamlModuleGroup(
            "nativeint_mod",
            listOf("54_nativeint_mod"),
            deps = listOf("arith", "boolean", "comparison", "float", "int32_mod", "option_mod", "str")
        ),
        OCamlModuleGroup(
            "int64_mod",
            listOf("47_int64_mod"),
            deps = listOf("arith", "boolean", "comparison", "float", "int32_mod", "nativeint_mod", "option_mod", "str")
        ),
        OCamlModuleGroup("atomic_mod", listOf("23_atomic_mod"), deps = listOf("arith", "boolean", "comparison", "str", "unit")),
        OCamlModuleGroup(
            "complex_mod", listOf("29_complex_mod"), deps = listOf("arith", "boolean", "comparison", "float")
        ),
        OCamlModuleGroup("uchar_mod", listOf("73_uchar_mod"), deps = listOf("arith", "boolean", "char", "comparison")),
        OCamlModuleGroup(
            "filename_mod",
            listOf("37_filename_mod"),
            deps = listOf("boolean", "comparison", "list", "option_mod", "pair_mod", "str", "unit")
        ),
        OCamlModuleGroup(
            "list_ops", listOf("12_list"), deps = listOf("arith", "boolean", "comparison", "list", "str")
        ),
        // lazy_mod's examples pass read_line, read_int and read_float to Lazy.from_fun
        OCamlModuleGroup(
            "stdin", listOf("16_stdin"), deps = listOf("arith", "boolean", "comparison", "float", "option_mod", "str", "unit")
        ),
        OCamlModuleGroup(
            "lazy_mod",
            listOf("48_lazy_mod"),
            deps = listOf("arith", "boolean", "comparison", "fun_mod", "stdin", "str", "strconv")
        ),
        OCamlModuleGroup("repr_mod", listOf("77_repr_mod"), deps = listOf("arith", "boolean", "comparison", "str")),
        OCamlModuleGroup(
            "type_mod", listOf("72_type_mod"), deps = listOf("arith", "boolean", "comparison", "option_mod", "str", "unit")
        ),
        OCamlModuleGroup(
            "io", listOf("13_io"), deps = listOf("boolean", "char", "comparison", "float", "str", "unit")
        ),
        OCamlModuleGroup(
            "stderr",
            listOf("15_stderr"),
            deps = listOf("boolean", "char", "comparison", "float", "option_mod", "str", "string_mod", "unit")
        ),
        OCamlModuleGroup(
            "out",
            listOf("17_out"),
            deps = listOf(
                "boolean", "char", "comparison", "float", "io", "list", "option_mod", "str", "string_mod", "unit"
            )
        ),
        // Some examples pass the results of input functions to output ones
        OCamlModuleGroup(
            "in",
            listOf("18_in"),
            deps = listOf(
                "boolean", "char", "comparison", "float", "io", "list", "option_mod", "out", "str", "string_mod", "unit"
            )
        ),
        // The examples pass print_newline, print_string, print_int and flush_all to at_exit
        OCamlModuleGroup(
            "termination",
            listOf("21_termination"),
            deps = listOf("arith", "boolean", "comparison", "fun_mod", "out", "ref", "stdout", "str", "unit")
        ),
        // Their channels come from `stdin`, `stdout`, `open_in` and `open_out`. `String.to_bytes` and
        // `Int64.of_int` give the bytes and int64 values.
        OCamlModuleGroup(
            "in_channel_mod",
            listOf("44_in_channel_mod"),
            deps = listOf(
                "arith", "boolean", "char", "comparison", "fun_mod", "in", "int64_mod", "io", "list", "option_mod", "out", "str",
                "string_mod", "unit"
            )
        ),
        OCamlModuleGroup(
            "bytes_mod",
            listOf("26_bytes_mod"),
            deps = listOf(
                "arith", "boolean", "char", "char_mod", "comparison", "fun_mod", "int32_mod", "int64_mod", "list",
                "option_mod", "pair", "pair_mod", "str", "string_mod", "uchar_mod", "unit"
            )
        ),
        OCamlModuleGroup(
            "out_channel_mod",
            listOf("58_out_channel_mod"),
            deps = listOf(
                "arith", "boolean", "bytes_mod", "char", "comparison", "fun_mod", "in", "int64_mod", "io", "list", "option_mod",
                "out", "str", "string_mod", "unit"
            )
        ),
        OCamlModuleGroup(
            "float_mod",
            listOf("38_float_mod"),
            deps = listOf("arith", "boolean", "comparison", "float", "fun_mod", "list", "option_mod", "pair_mod", "unit")
        ),
        OCamlModuleGroup(
            "buffer_mod",
            listOf("25_buffer_mod"),
            deps = listOf(
                "arith", "boolean", "bytes_mod", "char", "char_mod", "comparison", "fun_mod", "int32_mod", "int64_mod",
                "io", "list", "option_mod", "pair", "pair_mod", "str", "string_mod", "uchar_mod", "unit"
            )
        ),
        OCamlModuleGroup("atomic_mod", listOf("23_atomic_mod"), deps = listOf("arith", "boolean", "comparison", "str", "unit")),
        OCamlModuleGroup(
            "array_mod",
            listOf("22_array_mod"),
            deps = listOf(
                "arith", "boolean", "comparison", "float", "list", "option_mod", "pair", "stdout", "str", "strconv", "unit"
            )
        ),
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
