package testutil

import oneast.Type
import query.Example
import query.Examples
import testutil.ocaml.OCamlChecker
import util.CheckingGroundTruthOracle
import util.GroundTruth
import java.io.File

fun minimalNegexs(
    negExamples: Collection<Example>,
    groundTruth: GroundTruth
): Set<Example> {
    val negSubs = buildSet {
        for (ex in negExamples) addAll(ex.subexprs().filter { !groundTruth.valid(it) })
    }
    return negSubs.filter { it.subexprs().none { sub -> sub != it && sub in negSubs } }.toSet()
}

fun splitExamples(examples: Collection<Example>, groundTruth: GroundTruth) =
    examples.partition { groundTruth.valid(it) }.let { it.first.toSet() to it.second.toSet() }

fun splitOCamlStrings(
    exampleFile: File,
    groundTruth: OCamlChecker,
    posOutFile: File,
    negOutFile: File
) {
    val examples = exampleFile.readText().lines().map { it.trim() }.filter { it.isNotEmpty() }
    groundTruth.checkAllParallel(examples).forEach {
        (if (it.isValid) posOutFile else negOutFile).appendText(
            it.expression + System.lineSeparator()
        )
    }
}

fun splitOCamlExamplesAndCheckConsistency(
    examples: Collection<Example>,
    checkerFromTypes: CheckingGroundTruthOracle,
    groundTruth: OCamlChecker
): Pair<Set<Example>, Set<Example>> {
    /** Ground truth from parsing OCaml types and checking using our own unification. */
    val (checkPos, checkNeg) = splitExamples(examples, checkerFromTypes)
    /** The ground truth given by the actual OCaml implementation. */
    val (realPos, realNeg) = splitExamples(examples, groundTruth)

    fun assureEq(byCheckerFromTypes: Set<Example>, byOCamlc: Set<Example>, pos: Boolean) =
        require(byCheckerFromTypes == byOCamlc) {
            val sign = if (pos) "pos" else "neg"
            "Warning: Oracle from parsed types disagrees with ocamlc ground truth:\n" +
                    (byCheckerFromTypes - byOCamlc).let { if (it.isEmpty()) "" else "checker says $sign but ocamlc disagrees: $it" } +
                    (byOCamlc - byCheckerFromTypes).let { if (it.isEmpty()) "" else "ocamlc says $sign but checker disagrees: $it" }
        }

    assureEq(checkPos, realPos, true)
    assureEq(checkNeg, realNeg, false)

    return realPos to realNeg
}

fun sanityCheck(state: Map<String, Type>, examples: Examples) {
    val oracle = CheckingGroundTruthOracle(state)
    examples.posNoSubexprs.forEach {
        if (it.names.all { it in state } && !oracle.valid(it)) println("Failed posex $it")
    }
    examples.neg.forEach {
        if (it.names.all { it in state } && oracle.valid(it)) println("Failed negex $it")
    }
}
