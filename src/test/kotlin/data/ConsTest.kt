package data

import query.AbstractQuery
import query.Examples
import util.ScrappyNewOracle
import util.io.signedExample
import util.io.signedExamplesFromStrings

object ConsTest : AbstractQuery() {
    override val name = "Cons"

    private val intExamples =
        mapOf(
            "(+ 0)" to "int",
            "(+ Li)" to "lint",
            "(+ LLi)" to "llint",
            "(+ cons)" to "f",
            "(+ (cons 0))" to "lint to lint",
            "(+ (cons 0 Li))" to "lint",
            "(+ (cons 0 (cons 0 Li)))" to "lint",
            "(+ (cons Li))" to "llint to llint",
            "(+ (cons Li LLi))" to "llint",
            "(+ (cons Li (cons Li LLi)))" to "llint",
            "(- (cons Li 0))" to null,
            "(- (cons LLi Li))" to
                    null, // had to add this or else we make (Li, L2([L0()])), (LLi, L2([L0()])), (cons,
            // [3_0]->[L2([L0()])]->[L2([L0()])])
            // The following two had to be added for correctness in label equiv classes, but seem a
            // little excessive
            "(+ (cons LLi))" to "lllint to lllint",
            "(+ (cons (cons 0 Li)))" to "llint to llint",
            //        "(+ (cons cons))" to "lf to lf",
        )
    private val boolExamples =
        mapOf(
            "(+ tr)" to "bool",
            "(+ Lb)" to "lbool",
            "(+ (cons tr))" to "lbool to lbool",
            "(+ (cons tr Lb))" to "lbool",
            "(+ (cons tr (cons tr Lb)))" to "lbool",
            "(- (cons 0 Lb))" to null,
            "(- (cons tr Li))" to null,
            "(- (cons 0 LLi))" to null,
            "(- (cons tr LLi))" to null,
            "(- (cons tr (cons 0 Li)))" to null,
            "(+ (cons Lb))" to "llbool to llbool"
        )
    private val exs = intExamples + boolExamples

    override val examples: Examples = signedExamplesFromStrings(exs.keys)
    override val oracle = ScrappyNewOracle(exs.mapKeys { signedExample(it.key) })
}
