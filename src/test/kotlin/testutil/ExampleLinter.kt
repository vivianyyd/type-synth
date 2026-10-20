package testutil

import query.Example
import query.Examples
import testutil.ocaml.OCamlChecker
import util.CheckingGroundTruthOracle
import util.GroundTruth

/**
 * Splits valid and invalid [examples], checking against *both* our own typechecker equipped with
 * the declared type signatures, and the ocamlc ground truth. Ensures negative examples are minimal.
 *
 * Leaves out examples with lambdas or lets, since our typechecker cannot check them yet. Their
 * subexpressions without binders are kept.
 */
fun splitOCamlExamples(
    examples: Collection<Example>,
    checkerFromTypes: CheckingGroundTruthOracle,
    groundTruth: OCamlChecker
): Examples {
    fun splitExamples(
        examples: Collection<Example>,
        groundTruth: GroundTruth
    ): Pair<Set<Example>, Set<Example>> {
        val (pos, neg) =
            examples.flatMap { it.subexprs() }.filterNot { it.hasBinders() }.toSet()
                .partition { groundTruth.valid(it) }
        val minNeg = neg.filter { it.subexprs().dropLast(1).none { sub -> sub in neg } }
        return pos.toSet() to minNeg.toSet()
    }

    /** Ground truth from parsing OCaml types and checking using our own unification. */
    val (checkPos, checkNeg) = splitExamples(examples, checkerFromTypes)
    /** The ground truth given by the actual OCaml implementation. */
    val (realPos, realNeg) = splitExamples(examples, groundTruth)

    fun assureEq(byCheckerFromTypes: Set<Example>, byOCamlc: Set<Example>, pos: Boolean) =
        require(byCheckerFromTypes == byOCamlc) {
            val sign = if (pos) "pos" else "neg"
            "Warning: Oracle from parsed types disagrees with ocamlc ground truth:\n" +
                    (byCheckerFromTypes - byOCamlc).let {
                        if (it.isEmpty()) "" else "checker says $sign but ocamlc disagrees: $it"
                    } +
                    (byOCamlc - byCheckerFromTypes).let {
                        if (it.isEmpty()) "" else "ocamlc says $sign but checker disagrees: $it"
                    }
        }

    assureEq(checkPos, realPos, true)
    assureEq(checkNeg, realNeg, false)

    return Examples(realPos, realNeg)
}
