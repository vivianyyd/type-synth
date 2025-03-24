package symbolicgen

import util.*
import java.io.File

fun main() {
    val sketchPath = listOf("src", "main", "sketch", "symbolicgen", "generated").joinToString(
        separator = File.separator,
        postfix = File.separator
    )
//    val out = PrintWriter(FileOutputStream(sketchPath + "scratchpad.sk"))
//    out.println("hello")
//    out.close()

    val consExamples = mapOf(
        "(+ 0)" to "int",
        "(+ tr)" to "bool",
        "(+ []i)" to "lint",
        "(+ []b)" to "lbool",
        "(+ [[]]i)" to "llint",
        "(+ (cons 0))" to "lint to lint",
        "(+ (cons 0 []i))" to "lint",
        "(+ (cons 0 (cons 0 []i)))" to "lint",
//        "(+ (cons tr []b))" to "lbool",
//        "(+ (cons tr (cons tr []b)))" to "lbool",
//        "(+ (cons []i [[]]i))" to "llint",
//        "(+ (cons []i (cons []i [[]]i)))" to "llint",
//        "(- (cons tr []i))" to null,
//        "(- (cons []i 0))" to null,
//        "(- (cons 0 []b))" to null,
//        "(- (cons 0 [[]]i))" to null,
//        "(- (cons tr [[]]i))" to null,
//        "(- (cons tr (cons 0 []i)))" to null,
    )
    val query = parseNewExamples(consExamples.keys)
    val b = SymbolicTypeBuilder(query)
    b.readAllExamples()
    b.s.printState()
    EncodeUnrolledUnif(query, b.s).make()
}

class EncodeUnrolledUnif(val query: NewQuery, val state: State) {
    private val w = Writer()

    private var fresh = 0
    private val sketchNames = mutableMapOf<String, String>()

    init {
        query.names.forEach { n ->
            val name = "_${n.filter { it.isLetterOrDigit() }}"
            if (name !in sketchNames.values) sketchNames[n] = name
            else sketchNames[n] = name + "_${fresh++}"
        }
    }

    /** Use me wisely */
    private fun sk(name: String) = sketchNames[name]!!
    private fun gen(name: String) = "${sk(name)}_gen"

    fun make() {
        header()
        query.names.forEach { generator(it) }
        query.posExamples.forEach { posExample(it) }
        println(w.s()) // TODO
    }

    private fun header() {
        w.include("/home/vivianyyd/type-synth/src/main/sketch/symbolicgen/types.sk")
        w.include("/home/vivianyyd/applications/sketch-1.7.6/sketch-frontend/sketchlib/list.skh")
        w.comment(listOf("NAME\t\tDUMMY") + sketchNames.map { (k, v) -> "$k\t\t\t$v" })
    }

    private fun choose(portSketchName: String, options: List<SymbolicType>) {
        val flag = "flag_$portSketchName"
        // TODO not sure if this is right. we didn't see anything that forced us to make this a function so anything but arrow is ok
        val opts = options.ifEmpty { listOf(Variable(), Label()) }
        if (opts.size == 1) {
            pickOption(portSketchName, opts[0])  // Makes code shorter
            return
        }
        w.lines(
            listOf(
                "int $flag = ??",
                "assert (${(opts.indices).joinToString(separator = " || ") { "$flag == $it" }})"
            )
        )
        opts.forEachIndexed { i, t ->
            w.block("if ($flag == $i)") { pickOption(portSketchName, t) }
        }
    }

    private fun pickOption(portSketchName: String, t: SymbolicType) = when (t) {
        is Label -> w.lines(
            listOf(
                "$portSketchName = new Label()",
                "canBeBoundInLabel = true"
            )
        )
        is Variable -> w.lines(
            listOf(
                "List<Var> bindings",
                "if (!(canBeFresh || canBeBoundInLabel)) bindings = vars",
                "$portSketchName = new Var(possBindings=bindings)",
                "vars = add(vars, (Var)$portSketchName)",
            )
        )
        is Function -> {
            val leftName = "${portSketchName}l"
            val riteName = "${portSketchName}r"
            w.lines(
                listOf(
                    "Type $leftName; Type $riteName",
                    "canBeFresh = true"
                )
            )
            choose(leftName, t.left)
            w.line("canBeFresh = false")
            choose(riteName, t.rite)
            w.line("$portSketchName = new Function(left=$leftName, rite=$riteName)")
        }
        is Error, is Hole -> throw Exception("nah")
    }

    private fun generator(name: String) =
        w.block("generator Type ${gen(name)}()") {
            val options = state.read()[name]!!
            if (options.size == 1 && options[0] is Label) w.line("return new Label()")  // Makes code shorter
            else {
                w.lines(
                    listOf(
                        "Type root",
                        "boolean canBeFresh = false",
                        "boolean canBeBoundInLabel = false",
                        "List<Var> vars = empty()"
                    )
                )
                choose("root", options)
                w.line("return root")
            }
        }

    private fun exToSketch(ex: Example): String = when (ex) {
        is Name -> sk(ex.name)
        is App -> "oo${exToSketch(ex.fn)}co${exToSketch(ex.arg)}cc"
    }

    private fun posExample(ex: Example) = when (ex) {
        is Name -> w.block("harness Type ${exToSketch(ex)}()") { w.line("return ${gen(ex.name)}()") }
        is App -> w.block("harness Type ${exToSketch(ex)}()") {
            w.lines(
                listOf(
                    "assert (isFunction(${exToSketch(ex.fn)}()))",
                    "assert (leq(${exToSketch(ex.arg)}(), ((Function)${exToSketch(ex.fn)}()).left))",
                    // TODO Here we compute possible variable bindings performed by zero.
                    //  A Var must store things it could be bound by. Then in leq we can reason about possible binders
                    "return ((Function)${exToSketch(ex.fn)}()).rite"
                )
            )
        }
    }
    // TODO First just do the whole tree and see how it goes. Probably bad.
    //      Then do variable bindings. Hope it just works, and constraints I do explicitly are implicit in Sketch.
    //      If not, then see if we need to explicitly help it number the nodes and make constraints for itself
    //      For variable binding reasoning, could give each V/L an id field so we can refer to them
    //        Or since we construct them nestedly, each V field can just store pointers or inds
    //        of nodes that could've bound them
    //       ^^^^THIS OK BUT EACH TYPE MUST STORE A ID, SINCE == ON ADT IS STRUCTURAL NOT PHYSICAL.
    //       STRUCTS ARE TOO EXPENSIVE EVEN THO THEY USE PHYSICAL EQUALS.

    // TODO use canBeFresh and canBeBoundInLabel. If either is true, make list of possBindings empty
    //      then when checking individual examples, if the list is NULL (vs empty?) it passes like a freshVar
    //      if the list is not empty then the type of the thingy must be equal to one of the possBindings
    //      need to keep context when checking examples. Could iterate down type/thru list of bindings and keep a map
    //      could also map params in example to vars they're bound to and iterate thru that list instead
    //      typeeq oracle should be put in with dummies for values, like how I handled len in s4s

    // TODO maintain a list of vars chosen so far. Vars can store what they could be
    //   when checking individual examples, we can see if it's satisfiable that the thing passed
    //   in one place is equal to any of the things that the var says it could be (when checking examples,
    //   as we read args we need to bind variables to them to refer to later when we check possible var equality)
    //   how to deal with labels? In particular, if none of the var bindings work, the prev choice must be label
    //   it should fall out from just the var selection being UNSAT!
    /*
    generator calls for each name (microopt that might be unnecessary: if only one choice, short circuit to directly produce it)

    for each example, hard-code how to unify it:
    order all examples by subexpressions
    TODO what's the most efficient way to memoize computations in sketch?

    type-expr-dummy-name... type-expr-dummy-name
        they are functions that call the generator dummies
    and they call each other for subexpr references

    TODO how to deal with variable bindings?

    CHECK cons 0 []i
        CHECK cons 0
            CHECK cons
            ASSERT cons is ->
            CHECK 0
            ASSERT 0 < cons param type
        ASSERT cons 0 is ->
        CHECK []i
        ASSERT []i < cons 0 param type
     */
}

class Writer {
    private val sb = StringBuilder()
    private var indentLevel = 0

    fun indent() = indentLevel++
    fun dedent() = indentLevel--

    fun line(l: String) = lineNoSemi("$l;")

    private fun lineNoSemi(l: String) {
        repeat(indentLevel) { sb.append("\t") }
        sb.appendLine(l)
    }

    fun lines(l: List<String>) = l.forEach { line(it) }

    fun include(l: String) {
        line("include \"$l\"")
    }

    fun comment(l: List<String>) {
        lineNoSemi("/*")
        l.forEach { lineNoSemi(it) }
        lineNoSemi("*/")
    }

    fun block(header: String, buildBody: () -> Unit) {
        lineNoSemi("$header {")
        indent()
        buildBody()
        dedent()
        lineNoSemi("}")
    }

    fun s() = sb.toString()
}
