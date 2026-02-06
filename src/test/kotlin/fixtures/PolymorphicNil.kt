package fixtures

import query.Query
import query.parseApp
import query.parseExamples
import util.ScrappyNewOracle

object PolymorphicNil : Test {
    override val name = "PolymorphicNil"

    private val intExamples =
        mapOf(
            "(+ 0)" to "int",
            "(+ nil)" to "la",
            "(+ cons)" to "f",
            "(+ (cons 0))" to "lint to lint",
            "(+ (cons 0 nil))" to "lint",
            "(+ (cons 0 (cons 0 nil)))" to "lint",
            "(+ (cons nil))" to "la to la",
            "(+ (cons nil nil))" to "la",
            "(+ (cons nil (cons nil nil)))" to "lla",
            "(- (cons nil 0))" to null,
            // [3_0]->[L2([L0()])]->[L2([L0()])])
            // The following two had to be added for correctness in label equiv classes, but seem a
            // little excessive
            "(+ (cons (cons 0 nil)))" to "llint to llint",
            //        "(+ (cons cons))" to "lf to lf",
        )
    private val boolExamples =
        mapOf(
            "(+ tr)" to "bool",
            "(+ nil)" to "lbool",
            "(+ (cons tr))" to "lbool to lbool",
            "(+ (cons tr nil))" to "lbool",
            "(+ (cons tr (cons tr nil)))" to "lbool",
            "(- (cons nil tr))" to null,
            "(- (cons 0 (cons tr nil)))" to null,
            "(- (cons tr (cons 0 nil)))" to null,
        )
    val examples = intExamples + boolExamples

    override val query: Query = parseExamples(examples.keys)
    override val oracle = ScrappyNewOracle(examples.mapKeys { parseApp(it.key) })
}
