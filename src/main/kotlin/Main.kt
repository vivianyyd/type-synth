import symbolicgen.SymbolicTypeBuilder
import symbolicgen.concretesketcher.ConcreteSketcher
import symbolicgen.symbolicenumerator.SymbolicEnumerator
import test.ConsTest
import util.writeConcretizeInput

const val ROUNDS = 4
const val RUN_SKETCH = true

fun main() {
    val test = ConsTest
    val query = test.query
    val oracle = test.oracle
    val b = SymbolicTypeBuilder(query).make

    b.printState()
    val enum = SymbolicEnumerator(query, b, oracle)
    val specializedSymbolicTypes = enum.enumerateAll()
    println(specializedSymbolicTypes.pr())
    specializedSymbolicTypes.forEachIndexed { i, t ->
        val sketcher = ConcreteSketcher(query, t, enum.varTypeIds, oracle)
        writeConcretizeInput(sketcher.query(), "test$i")
    }

//    val out = if (RUN_SKETCH) callSketch(sketcher.sketchInput(), "test") else readSketchOutput("test")
//    val (types, time) = (sketcher.parse(out))
//    println("${types.size} types in $time seconds")
}

fun <T> List<T>.pr() = this.joinToString(separator = "\n")
