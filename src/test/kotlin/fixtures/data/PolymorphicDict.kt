package fixtures.data

import fixtures.Test
import products.types.parseType
import query.Query
import util.CheckingOracle
import util.io.parseExamples

object PolymorphicDict : Test {
    override val name = "Dict"
    private val basics =
        listOf(
            "(+ 0)",
            "(+ 1)",
            "(+ tr)",
            "(+ {})",
            "(+ put)",
        )
    private val put =
        listOf(
            "(+ (put {}))",
            "(+ (put {} 0))",
            "(+ (put {} 1))",
            "(+ (put {} 0 tr))",
            "(+ (put (put {} 0 tr)))",
            "(+ (put (put {} 1 tr)))",
            "(+ (put (put {} 0 tr) 0))",
            "(+ (put (put {} 0 tr) 1))",
            "(+ (put (put {} 1 tr) 1))",
            "(+ (put (put {} 0 tr) 0 tr))",
            "(+ (put (put {} 0 tr) 1 tr))",
            "(+ (put (put {} 1 tr) 1 tr))",
            ////////////
            "(+ (put {}))",
            "(+ (put {} tr))",
            "(+ (put {} tr 0))",
            "(+ (put (put {} tr 0)))",
            "(+ (put (put {} tr 0) tr))",
            "(+ (put (put {} tr 0) tr 0))",
            "(+ (put (put {} tr 1) tr 0))",
            "(+ (put (put {} tr 1) tr))",
            "(+ (put (put {} tr 1) tr 1))",
            //////////
            //        "(+ (put {}))",
            //        "(+ (put {} tr))",
            //        "(+ (put {} tr tr))",
            //        "(+ (put (put {} tr tr)))",
            //        "(+ (put (put {} tr tr) tr))",
            //        "(+ (put (put {} tr tr) tr tr))",
            //        //////////
            "(+ (put {}))",
            "(+ (put {} 0 1))",
            "(+ (put {} 1 0))",
            "(+ (put {} 1 1))",
            "(+ (put (put {} 0 0)))",
            "(+ (put (put {} 1 0)))",
            "(+ (put (put {} 0 1) 0))",
            "(+ (put (put {} 0 1) 1))",
            "(+ (put (put {} 1 0) 1))",
            "(+ (put (put {} 0 0) 0 1))",
            "(+ (put (put {} 0 0) 1 0))",
            "(+ (put (put {} 1 0) 1 1))",

            ////////////
            "(- (put 0))",
            "(- (put tr))",
            "(- (put 1))",
            "(- (put (put {})))",
            "(- (put (put {} tr)))",
            "(- (put (put {})))",
            "(- (put (put {} 0)))",
            "(- (put (put {} 0 tr) 0 0))",
            "(- (put (put {} 0 tr) tr))",
            "(- (put (put {} 0 1) tr))",
            "(- (put (put {} 0 1) 1 tr))",
            "(- (put (put {} tr 1) 0))",
            "(- (put (put {} tr 1) tr tr))",
        )

    // TODO next: chain operator takes dicts ab, bc and produces ac

    val examples = basics + put

    override val query: Query = parseExamples(examples)
    override val oracle =
        CheckingOracle(
            mapOf(
                "0" to "(i)",
                "1" to "(i)",
                "tr" to "(b)",
                "{}" to "(d a b)",
                "put" to "(-> (d k v) (-> k (-> v (d k v))))"
            )
                .mapValues { parseType(it.value) })
}
