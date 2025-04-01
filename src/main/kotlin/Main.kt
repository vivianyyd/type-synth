import symbolicgen.SymbolicTypeBuilder
import symbolicgen.symbolicenumerator.SymbolicEnumerator
import test.IdTest

const val ROUNDS = 4
const val RUN_SKETCH = true

fun main() {
    val query = IdTest.query
    val oracle = IdTest.oracle
    val b = SymbolicTypeBuilder(query).make

    b.printState()
    val enum = SymbolicEnumerator(query, b).enumerateAll()
    println(enum.pr())

//    val out = if (RUN_SKETCH) callSketch(sketcher.sketchInput(), "test") else readSketchOutput("test")
//    val (types, time) = (sketcher.parse(out))
//    println("${types.size} types in $time seconds")
}

fun <T> List<T>.pr() = this.joinToString(separator = "\n")
