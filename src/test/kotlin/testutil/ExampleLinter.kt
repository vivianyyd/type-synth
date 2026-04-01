package testutil

import oneast.Type
import query.Example
import query.Examples
import query.Query
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
    query: Query,
    groundTruth: OCamlChecker
): Pair<Set<Example>, Set<Example>> {
    val examples = query.examples.posNoSubexprs + query.examples.neg
    /** Ground truth from parsing OCaml types and checking using our own unification. */
    val (checkPos, checkNeg) = splitExamples(examples, query.oracle)
    /** The ground truth given by the actual OCaml implementation. */
    val (realPos, realNeg) = splitExamples(examples, groundTruth)

    fun assureEq(a: Set<Example>, b: Set<Example>) =
        require(a == b) {
            "Warning: oracle from parsed types disagrees with ground truth on ${(a - b) + (b - a)}"
        }

    assureEq(checkPos, realPos)
    assureEq(checkNeg, realNeg)

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
