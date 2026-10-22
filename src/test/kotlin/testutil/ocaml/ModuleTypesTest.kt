package testutil.ocaml

import oneast.Arrow
import oneast.Type
import query.Name
import org.junit.jupiter.api.io.TempDir
import testutil.unsignedExample
import util.CheckingGroundTruthOracle
import java.io.File
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotEquals
import kotlin.test.assertTrue

/** How [parseTypesFile] names the types of modules: each its own, unless it renames another. */
class ModuleTypesTest {
    @TempDir
    lateinit var dir: File

    private val parser = OcamlTypeParser()

    private fun write(name: String, text: String) = File(dir, name).writeText(text.trimIndent() + "\n")

    /** Every file in [dir], parsed with [parser]. */
    private fun load(): Map<String, Type> =
        dir.listFiles()!!.sorted().flatMap { parseTypesFile(parser, it).entries }.associate { it.key to it.value.type }

    /** [sig] parsed with [parser], so that its labels are comparable with [load]'s. */
    private fun type(sig: String): Type = parser.parseSignatures("val x : $sig").getValue("x")

    private fun Type.result() = (this as Arrow).r

    @Test
    fun `a type that renames another is that type`() {
        write("1_char_mod.types", "// Char\n// type t = char\nval chr : int -> t")
        write("2_option_mod.types", "// Option\n// type 'a t = 'a option = None | Some of 'a\nval some : 'a -> 'a t")
        write(
            "3_result_mod.types",
            "// Result\n// type ('a, 'e) t = ('a, 'e) result = Ok of 'a | Error of 'e\nval ok : 'a -> ('a, 'e) t"
        )
        write("4_unit_mod.types", "// Unit\n// type t = unit = ()\nval to_string : t -> string")
        write("5_in_mod.types", "// In\n// type t = Stdlib.in_channel\nval input_char : t -> char option")
        write("6_iarray_mod.types", "// Iarray\n// type +'a t = 'a iarray\nval length : 'a t -> int")
        val types = load()
        assertEquals(type("int -> char"), types["Char.chr"])
        assertEquals(type("'a -> 'a option"), types["Option.some"])
        assertEquals(type("'a -> ('a, 'e) result"), types["Result.ok"])
        assertEquals(type("unit -> string"), types["Unit.to_string"])
        assertEquals(type("in_channel -> char option"), types["In.input_char"])
        assertEquals(type("'a iarray -> int"), types["Iarray.length"])
    }

    @Test
    fun `a type that renames another is that type in other files too`() {
        write("1_char_mod.types", "// Char\n// type t = char")
        write("2_basics.types", "val code : Char.t -> int")
        write("3_uchar_mod.types", "// Uchar\nval of_char : Char.t -> t")
        val types = load()
        assertEquals(type("char -> int"), types["code"])
        assertEquals(type("char"), (types.getValue("Uchar.of_char") as Arrow).l)
    }

    @Test
    fun `each module has its own abstract types`() {
        write("1_mutex_mod.types", "// Mutex\n// type t\nval create : unit -> t")
        write("2_buffer_mod.types", "// Buffer\n// type t\nval create : int -> t")
        write("3_condition_mod.types", "// Condition\n// type t\nval create : unit -> t\nval wait : t -> Mutex.t -> unit")
        val types = load()
        val mutex = types.getValue("Mutex.create").result()
        val buffer = types.getValue("Buffer.create").result()
        val condition = types.getValue("Condition.create").result()
        assertEquals(3, setOf(mutex, buffer, condition).size)
        assertEquals(type("Condition.t -> Mutex.t -> unit"), types["Condition.wait"])
        assertEquals(mutex, (types.getValue("Condition.wait").result() as Arrow).l)
    }

    @Test
    fun `a declaration that does not rename a type is a type of its own`() {
        write("1_domain_mod.types", "// Domain\n// type id = private int\nval self : unit -> id")
        write("2_seq_mod.types", "// Seq\n// type 'a t = unit -> 'a node\nval empty : 'a t")
        write("3_complex_mod.types", "// Complex\n// type t = { re : float; im : float }\nval zero : t")
        write("4_either_mod.types", "// Either\n// type ('a, 'b) t = Left of 'a | Right of 'b\nval left : 'a -> ('a, 'b) t")
        write("5_swap_mod.types", "// Swap\n// type ('a, 'b) t = ('b, 'a) result\nval x : ('a, 'b) t")
        write("6_pair_mod.types", "// Pair\n// type ('a, 'b) t = 'a * 'b\nval x : ('a, 'b) t")
        load()
        val expected = listOf("Domain.id", "Seq.t", "Complex.t", "Either.t", "Swap.t", "Pair.t")
        assertEquals(emptyList(), expected - parser.constructorNames)
        assertTrue(listOf("int", "node", "result").none { it in parser.constructorNames })
    }

    @Test
    fun `a type in a submodule is the module's`() {
        write("1_domain_mod.types", "// Domain\nval DLS.new_key : (unit -> 'a) -> 'a DLS.key")
        write("2_dls_mod.types", "// DLS\n// type 'a key\nval x : 'a key")
        write("3_obj_mod.types", "// Obj\nval Ephemeron.create : int -> Ephemeron.t\nval e : Seq.t")
        load()
        val expected = listOf("Domain.DLS.key", "DLS.key", "Obj.Ephemeron.t", "Seq.t")
        assertEquals(emptyList(), expected - parser.constructorNames)
    }

    @Test
    fun `every type in the stdlib signatures is predefined or a module's`() {
        ocamlTypesDir.listFiles()!!.filter { it.extension == "types" }.forEach { parseTypesFile(parser, it) }
        // The types ocamlc knows with -nopervasives, then the ones Stdlib declares.
        val predefined = setOf(
            "int", "char", "string", "bytes", "float", "bool", "unit", "exn", "array", "iarray",
            "list", "option", "int32", "int64", "nativeint", "lazy_t", "extension_constructor",
            "floatarray", "eff",
            "result", "ref", "in_channel", "out_channel", "open_flag", "fpclass", "format", "format4",
            "format6",
        )
        // `*2` and so on are tuples, and a qualified name is a module's.
        val others = parser.constructorNames.filter { !it.startsWith("*") && '.' !in it && it !in predefined }
        assertEquals(emptyList<String>(), others)
    }

    @Test
    fun `every name the stdlib signatures declare exists in OCaml`() {
        val ocaml = OCamlGroundTruth.default.create(stdlibSource)
        val missing = ocamlTypesDir.listFiles()!!.filter { it.extension == "types" }.sorted().flatMap { file ->
            parseTypesFile(parser, file).keys.filter { !ocaml.valid(Name(it)) }.map { "${file.name}: $it" }
        }
        assertEquals(emptyList<String>(), missing)
    }

    @Test
    fun `stdlib module types type-check as OCaml does`() {
        val oracle = CheckingGroundTruthOracle(
            ocamlTypesDir.listFiles()!!.filter { it.extension == "types" }
                .flatMap { parseTypesFile(parser, it).entries }.associate { it.key to it.value.type }
        )
        val ocaml = OCamlGroundTruth.default.create(stdlibSource)
        val valid = listOf(
            "(Char.equal Char Char)", "(Int32.add Int32.zero (Int32.of_int Num))", "(String.length Str)",
            "(Unit.equal Unit Unit)", "(Mutex.lock (Mutex.create Unit))",
            "(Condition.wait (Condition.create Unit) (Mutex.create Unit))",
            "(List.of_seq (Seq.return Num))", "(Option.is_some (Option.some Num))",
            "(Bytes.length (Bytes.create Num))", "(Buffer.length (Buffer.create Num))",
            "(Sys.signal_to_string Num)", "(Hashtbl.add (Hashtbl.create Num) Num Str)",
        )
        val invalid = listOf(
            "(Mutex.lock (Condition.create Unit))", "(Buffer.length (Bytes.create Num))",
            "(Int32.add Num Num)", "(Char.equal Str Char)", "(Queue.length (Stack.create Unit))",
            "(List.of_seq (List.cons Num Nil))",
        )
        for (s in valid) {
            assertTrue(oracle.valid(unsignedExample(s)), "checker rejects $s")
            assertTrue(ocaml.valid(unsignedExample(s)), "OCaml rejects $s")
        }
        for (s in invalid) {
            assertTrue(!oracle.valid(unsignedExample(s)), "checker accepts $s")
            assertTrue(!ocaml.valid(unsignedExample(s)), "OCaml accepts $s")
        }
    }
}
