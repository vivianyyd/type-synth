package testutil

import query.Example
import query.Examples
import util.CheckingGroundTruthOracle
import util.GroundTruth

/**
 * Splits valid and invalid [examples], checking against *both* our own typechecker equipped with
 * the declared type signatures, and OCaml itself. Ensures negative examples are minimal.
 */
fun splitOCamlExamples(
    examples: Collection<Example>,
    checkerFromTypes: CheckingGroundTruthOracle,
    groundTruth: GroundTruth
): Examples {
    fun splitExamples(
        examples: Collection<Example>,
        groundTruth: GroundTruth
    ): Pair<Set<Example>, Set<Example>> {
        val (pos, neg) =
            examples.flatMap { it.subexprs() }.toSet().partition { groundTruth.valid(it) }
        val minNeg = neg.filter { it.subexprs().dropLast(1).none { sub -> sub in neg } }
        return pos.toSet() to minNeg.toSet()
    }

    /** Ground truth from parsing OCaml types and checking using our own unification. */
    val (checkPos, checkNeg) = splitExamples(examples, checkerFromTypes)
    /** The ground truth given by the actual OCaml implementation. */
    val (realPos, realNeg) = splitExamples(examples, groundTruth)

    fun assureEq(byCheckerFromTypes: Set<Example>, byOCaml: Set<Example>, pos: Boolean) =
        require(byCheckerFromTypes == byOCaml) {
            val sign = if (pos) "pos" else "neg"
            "Warning: Oracle from parsed types disagrees with the OCaml ground truth:\n" +
                    (byCheckerFromTypes - byOCaml).let {
                        if (it.isEmpty()) "" else "checker says $sign but OCaml disagrees: $it"
                    } +
                    (byOCaml - byCheckerFromTypes).let {
                        if (it.isEmpty()) "" else "OCaml says $sign but checker disagrees: $it"
                    }
        }

    assureEq(checkPos, realPos, true)
    assureEq(checkNeg, realNeg, false)

    return Examples(realPos, realNeg)
}
