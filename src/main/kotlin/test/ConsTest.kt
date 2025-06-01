package test

import util.Query
import util.ScrappyNewOracle
import util.parseNewApp
import util.parseNewExamples

object ConsTest {
    private val intExamples = mapOf(
        "(+ 0)" to "int",
        "(+ Li)" to "lint",
        "(+ LLi)" to "llint",
        "(+ cons)" to "f",
//        "(+ (cons cons))" to "lf to lf",
        "(+ (cons 0))" to "lint to lint",
        "(+ (cons 0 Li))" to "lint",
        "(+ (cons 0 (cons 0 Li)))" to "lint",
        "(+ (cons Li))" to "llint to llint",
        "(+ (cons Li LLi))" to "llint",
        "(+ (cons Li (cons Li LLi)))" to "llint",
        "(- (cons Li 0))" to null,
        "(- (cons LLi Li))" to null, // had to add this or else we make (Li, L2([L0()])), (LLi, L2([L0()])), (cons, [3_0]->[L2([L0()])]->[L2([L0()])])
        // The following two had to be added for correctness in label equiv classes, but seem a little excessive
        "(+ (cons LLi))" to "lllint to lllint",
        "(+ (cons (cons 0 Li)))" to "llint to llint",
    )
    private val boolExamples = mapOf(
        "(+ tr)" to "bool",
        "(+ []b)" to "lbool",
        "(+ (cons tr))" to "lbool to lbool",
        "(+ (cons tr []b))" to "lbool",
        "(+ (cons tr (cons tr []b)))" to "lbool",
        "(- (cons 0 []b))" to null,
        "(- (cons tr Li))" to null,
        "(- (cons 0 LLi))" to null,
        "(- (cons tr LLi))" to null,
        "(- (cons tr (cons 0 Li)))" to null,
    )
    val examples = intExamples// + boolExamples

    val query: Query = parseNewExamples(examples.keys)
    val oracle = ScrappyNewOracle(examples.mapKeys { parseNewApp(it.key) })
}
