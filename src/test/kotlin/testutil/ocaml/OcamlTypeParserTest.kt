package testutil.ocaml

import oneast.Arrow
import oneast.NamedLabel
import oneast.Type
import oneast.Variable
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class OcamlTypeParserTest {
    private fun parse(sig: String): Type =
        OcamlTypeParser().parseSignatures("val x : $sig").getValue("x")

    /** A [NamedLabel] regardless of its (encounter-order-dependent) label id. */
    private fun Type.asLabel(): NamedLabel = this as NamedLabel

    /** Parses both types within one parser, so that constructor labels are comparable. */
    private fun assertParsesLike(expected: String, actual: String) {
        val types = OcamlTypeParser().parseSignatures("val e : $expected\nval a : $actual")
        assertEquals(types.getValue("e"), types.getValue("a"))
    }

    @Test
    fun `postfix application is left-associative and applies to the preceding atom`() {
        // 'a list -> list applied to 'a, not 'a applied to list.
        val t = parse("'a list").asLabel()
        assertEquals(listOf(Variable(0)), t.params)

        // 'a list list == list (list 'a)
        val ll = parse("'a list list").asLabel()
        val inner = ll.params.single().asLabel()
        assertEquals(listOf(Variable(0)), inner.params)
        // Both applications use the same `list` constructor label.
        assertEquals(ll.label, inner.label)
    }

    @Test
    fun `arrows are right associative`() {
        val t = parse("'a -> 'b -> 'c")
        // 'a -> ('b -> 'c)
        val outer = t as Arrow
        assertEquals(Variable(0), outer.l)
        val inner = outer.r as Arrow
        assertEquals(Variable(1), inner.l)
        assertEquals(Variable(2), inner.r)
    }

    @Test
    fun `parentheses regroup arrows for higher-order functions`() {
        // ('a -> 'b) -> 'a list -> 'b list  (map)
        val t = parse("('a -> 'b) -> 'a list -> 'b list") as Arrow
        assertTrue(t.l is Arrow, "first argument should itself be a function type")
        val rest = t.r as Arrow
        assertEquals(listOf(Variable(0)), rest.l.asLabel().params)
        assertEquals(listOf(Variable(1)), rest.r.asLabel().params)
    }

    @Test
    fun `tuple types become a label with one parameter per component`() {
        // Parse within one parser so constructor labels are comparable.
        val parser = OcamlTypeParser()
        val types = parser.parseSignatures(
            """
            val p : 'a * 'b
            val t : 'a * 'b * 'c
            """.trimIndent()
        )
        val pair = types.getValue("p").asLabel()
        assertEquals(listOf(Variable(0), Variable(1)), pair.params)

        val triple = types.getValue("t").asLabel()
        assertEquals(listOf(Variable(0), Variable(1), Variable(2)), triple.params)

        // A pair and a triple are *different* constructors.
        assertTrue(pair.label != triple.label)
    }

    @Test
    fun `application binds tighter than tuple which binds tighter than arrow`() {
        // 'acc * 'b list == ('acc) * ('b list), nested under no arrow here.
        val t = parse("'acc * 'b list").asLabel()
        assertEquals(2, t.params.size)
        assertEquals(Variable(0), t.params[0]) // 'acc
        assertEquals(listOf(Variable(1)), t.params[1].asLabel().params) // 'b list

        // ('a * 'b) list == list of a pair.
        val listOfPair = parse("('a * 'b) list").asLabel()
        assertEquals(2, listOfPair.params.single().asLabel().params.size)
    }

    @Test
    fun `multi-parameter module-qualified constructors`() {
        // Parse within one parser so constructor labels are comparable.
        val parser = OcamlTypeParser()
        val types = parser.parseSignatures(
            """
            val e : ('b, 'c) Either.t
            val s : 'a Seq.t
            """.trimIndent()
        )
        // ('b, 'c) Either.t -> Either.t applied to two arguments.
        val t = types.getValue("e").asLabel()
        assertEquals(listOf(Variable(0), Variable(1)), t.params)

        // 'a Seq.t -> single-parameter module-qualified postfix application.
        val seq = types.getValue("s").asLabel()
        assertEquals(listOf(Variable(0)), seq.params)
        // Distinct constructors despite both ending in `.t`.
        assertTrue(t.label != seq.label)
    }

    @Test
    fun `constructor labels are shared across signatures within one parser`() {
        val parser = OcamlTypeParser()
        val types = parser.parseSignatures(
            """
            val hd : 'a list -> 'a
            val length : 'a list -> int
            """.trimIndent()
        )
        val hdList = ((types.getValue("hd")) as Arrow).l as NamedLabel
        val lengthList = ((types.getValue("length")) as Arrow).l as NamedLabel
        assertEquals(hdList.label, lengthList.label)
    }

    /** The List module's own signatures: arrows, hofs, modules, tuples, multiple params */
    @Test
    fun `parses signatures`() {
        fun lastResult(type: Type): Type =
            if (type is Arrow) lastResult(type.r) else type

        fun assertNamedLabel(type: Type, arity: Int) {
            assert(type is NamedLabel && type.params.size == arity) {
                "Expected a NamedLabel with $arity parameter(s) but got $type"
            }
        }

        val exsFileNames = listOf("4_arith", "0_basics", "2_boolean", "8_char", "1_comparison", "50_list_mod")
        val (_, oracleTypes) = loadFromExsFiles(exsFileNames)

        // List.map : ('a -> 'b) -> 'a list -> 'b list  — higher-order function + postfix `list`.
        val map = oracleTypes.getValue("List.map") as Arrow
        assert(map.l is Arrow) { "map's first argument should be a function type" }
        val mapRest = map.r as Arrow
        assertNamedLabel(mapRest.l, arity = 1) // 'a list
        assertNamedLabel(mapRest.r, arity = 1) // 'b list

        // List.partition : ('a -> bool) -> 'a list -> 'a list * 'a list  — tuple result.
        val partition = lastResult(oracleTypes.getValue("List.partition"))
        assertNamedLabel(partition, arity = 2) // ('a list * 'a list)

        // List.partition_map : ('a -> ('b, 'c) Either.t) -> 'a list -> 'b list * 'c list
        val partitionMap = oracleTypes.getValue("List.partition_map") as Arrow
        val either = lastResult((partitionMap.l as Arrow))
        assertNamedLabel(either, arity = 2) // ('b, 'c) Either.t

        // List.to_seq : 'a list -> 'a Seq.t  — single-parameter module-qualified postfix.
        val toSeq = oracleTypes.getValue("List.to_seq") as Arrow
        assertNamedLabel(toSeq.r, arity = 1) // 'a Seq.t

        // List.concat : 'a list list -> 'a list  — nested postfix application.
        val concat = oracleTypes.getValue("List.concat") as Arrow
        val outerList = concat.l as NamedLabel
        assertNamedLabel(outerList.params.single(), arity = 1) // inner 'a list
    }

    /** float's group, loaded after list's: float must not get list's id (as with a fresh parser). */
    @Test
    fun `a shared parser keeps label ids apart across loads`() {
        val parser = OcamlTypeParser()
        val (_, fixedTypes) =
            loadFromExsFiles(ocamlModuleGroups.takeWhile { "6_float" !in it }.flatten(), parser)
        val (_, desiredTypes) = loadFromExsFiles(listOf("6_float"), parser)
        assertEquals(fixedTypes.getValue("Num").asLabel().label, desiredTypes.getValue("Num").asLabel().label)
        assertTrue(desiredTypes.getValue("Flt").asLabel().label != fixedTypes.getValue("Nil").asLabel().label)
    }

    @Test
    fun `labelled arguments parse as their unlabelled type`() {
        assertParsesLike(
            "'a -> ('b -> 'a) -> 'b option -> 'a",
            "none:'a -> some:('b -> 'a) -> 'b option -> 'a"
        )
        // The label is not mistaken for a constructor when its type is not parenthesized.
        assertParsesLike("'a option -> 'a -> 'a", "'a option -> default:'a -> 'a")
        assertParsesLike(
            "formatter -> string * int -> unit",
            "formatter -> fits:(string * int) -> unit"
        )
    }

    @Test
    fun `optional arguments are left out`() {
        assertParsesLike("int -> ('a, 'b) t", "?random:bool -> int -> ('a, 'b) t")
        assertParsesLike(
            "formatter -> 'a list -> unit",
            "?pp_sep:(formatter -> unit) -> formatter -> 'a list -> unit"
        )
        assertParsesLike(
            "string -> string list -> string",
            "string -> ?stdin:string -> string list -> string"
        )
        // A variable only the optional argument has takes up no id
        assertParsesLike("'a list -> 'a", "?cmp:('b -> 'b -> int) -> 'a list -> 'a")
    }

    private fun labels(sig: String) =
        OcamlTypeParser().parseSignaturesWithLabels("val x : $sig").getValue("x").labels

    @Test
    fun `each parameter's label is kept, and optional ones have none`() {
        assertEquals(listOf(null, "default"), labels("'a option -> default:'a -> 'a"))
        assertEquals(listOf("none", "some", null), labels("none:'a -> some:('b -> 'a) -> 'b option -> 'a"))
        assertEquals(listOf(null), labels("?random:bool -> int -> ('a, 'b) t"))
        assertEquals(listOf(null, null), labels("('a -> 'b) -> 'a list -> 'b list"))
        assertEquals(emptyList(), labels("int"))
    }

    @Test
    fun `an argument type's own labels are not the value's`() {
        assertEquals(listOf(null, null), labels("(f:int -> int) -> int -> int"))
    }

    @Test
    fun `comments are ignored`() {
        val types = OcamlTypeParser().parseSignatures(
            """
            // Ref
            val ref : 'a -> 'a ref
            val (!) : 'a ref -> 'a  // Equivalent to fun r -> r.contents.
            """.trimIndent()
        )
        assertEquals(listOf("ref", "(!)"), types.keys.toList())
        val deref = types.getValue("(!)") as Arrow
        assertEquals(listOf(Variable(0)), deref.l.asLabel().params)
        assertEquals(Variable(0), deref.r)
    }

    @Test
    fun `a comment may hold anything, even a signature we cannot parse`() {
        val types = OcamlTypeParser().parseSignatures(
            """
            // type t = { re : float; im : float }
            // val copy : (< .. > as 'a) -> 'a
              // indented: 'a -> 'b
            val length : 'a list -> int// no space before the comment
            val (^) : string -> string -> string // a -> b : c
            """.trimIndent()
        )
        assertEquals(listOf("length", "(^)"), types.keys.toList())
        assertEquals(parse("'a list -> int"), types.getValue("length"))
    }

    @Test
    fun `a file of only comments declares nothing`() {
        assertEquals(emptyMap(), OcamlTypeParser().parseSignatures("// Oo\n// val id : < .. > -> int\n"))
    }

    @Test
    fun `operator names may contain a colon`() {
        val types = OcamlTypeParser().parseSignatures(
            """
            val (:=) : 'a ref -> 'a -> unit
            val set : 'a ref -> 'a -> unit
            """.trimIndent()
        )
        assertEquals(types.getValue("set"), types.getValue("(:=)"))
    }
}
