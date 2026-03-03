package data

import query.AbstractQuery
import query.Examples
import util.ScrappyNewOracle
import util.io.signedExample
import util.io.signedExamplesFromStrings

object PolymorphicNil : AbstractQuery() {
    override val name = "PolymorphicNil"

    private val intExamples =
        mapOf(
            "(+ Num)" to "int",
            "(+ nil)" to "la",
            "(+ cons)" to "f",
            "(+ (cons Num))" to "lint to lint",
            "(+ (cons Num nil))" to "lint",
            "(+ (cons Num (cons Num nil)))" to "lint",
            "(+ (cons nil))" to "la to la",
            "(+ (cons nil nil))" to "la",
            "(+ (cons nil (cons nil nil)))" to "lla",
            "(- (cons nil Num))" to null,
            // [3_0]->[L2([L0()])]->[L2([L0()])])
            // The following two had to be added for correctness in label equiv classes, but seem a
            // little excessive
            "(+ (cons (cons Num nil)))" to "llint to llint",
            //        "(+ (cons cons))" to "lf to lf",
        )
    private val boolExamples =
        mapOf(
            "(+ true)" to "bool",
            "(+ nil)" to "lbool",
            "(+ (cons true))" to "lbool to lbool",
            "(+ (cons true nil))" to "lbool",
            "(+ (cons true (cons true nil)))" to "lbool",
            "(- (cons nil true))" to null,
            "(- (cons Num (cons true nil)))" to null,
            "(- (cons true (cons Num nil)))" to null,
        )
    private val exs = intExamples + boolExamples

    override val examples: Examples = signedExamplesFromStrings(exs.keys)
    override val oracle = ScrappyNewOracle(exs.mapKeys { signedExample(it.key) })
}
