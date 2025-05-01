package test

import util.NewQuery
import util.ScrappyNewOracle
import util.parseNewApp
import util.parseNewExamples

object ConsTest {
    private val intExamples = mapOf(
        "(+ 0)" to "int",
        "(+ []i)" to "lint",
        "(+ [[]]i)" to "llint",
        "(+ cons)" to "f",
//        "(+ (cons cons))" to "lf to lf",
        "(+ (cons 0))" to "lint to lint",
        "(+ (cons 0 []i))" to "lint",
        "(+ (cons 0 (cons 0 []i)))" to "lint",
        "(+ (cons []i))" to "llint to llint",
        "(+ (cons []i [[]]i))" to "llint",
        "(+ (cons []i (cons []i [[]]i)))" to "llint",
        "(- (cons []i 0))" to null,
        // The following two had to be added for correctness in label equiv classes, but seem a little excessive
        "(+ (cons [[]]i))" to "lllint to lllint",
        "(+ (cons (cons 0 []i)))" to "llint to llint",
    )
    private val boolExamples = mapOf(
        "(+ tr)" to "bool",
        "(+ []b)" to "lbool",
        "(+ (cons tr))" to "lbool to lbool",
        "(+ (cons tr []b))" to "lbool",
        "(+ (cons tr (cons tr []b)))" to "lbool",
        "(- (cons 0 []b))" to null,
        "(- (cons tr []i))" to null,
        "(- (cons 0 [[]]i))" to null,
        "(- (cons tr [[]]i))" to null,
        "(- (cons tr (cons 0 []i)))" to null,
    )
    val examples = intExamples// + boolExamples

    val query: NewQuery = parseNewExamples(examples.keys)
    val oracle = ScrappyNewOracle(examples.mapKeys { parseNewApp(it.key) })
}
