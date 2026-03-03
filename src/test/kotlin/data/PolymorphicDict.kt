package data

import products.types.parseType
import query.AbstractQuery
import query.Examples
import util.CheckingOracle
import util.io.signedExamplesFromStrings

object PolymorphicDict : AbstractQuery() {
    override val name = "Dict"
    private val basics =
        listOf(
            "(+ Num)",
            "(+ true)",
            "(+ {})",
            "(+ put)",
        )
    private val put =
        listOf(
            "(+ (put {}))",
            "(+ (put {} Num))",
            "(+ (put {} Num))",
            "(+ (put {} Num true))",
            "(+ (put (put {} Num true)))",
            "(+ (put (put {} Num true)))",
            "(+ (put (put {} Num true) Num))",
            "(+ (put (put {} Num true) Num))",
            "(+ (put (put {} Num true) Num))",
            "(+ (put (put {} Num true) Num true))",
            "(+ (put (put {} Num true) Num true))",
            "(+ (put (put {} Num true) Num true))",
            ////////////
            "(+ (put {}))",
            "(+ (put {} true))",
            "(+ (put {} true Num))",
            "(+ (put (put {} true Num)))",
            "(+ (put (put {} true Num) true))",
            "(+ (put (put {} true Num) true Num))",
            "(+ (put (put {} true Num) true Num))",
            "(+ (put (put {} true Num) true))",
            "(+ (put (put {} true Num) true Num))",
            //////////
            //        "(+ (put {}))",
            //        "(+ (put {} true))",
            //        "(+ (put {} true true))",
            //        "(+ (put (put {} true true)))",
            //        "(+ (put (put {} true true) true))",
            //        "(+ (put (put {} true true) true true))",
            //        //////////
            "(+ (put {}))",
            "(+ (put {} Num Num))",
            "(+ (put {} Num Num))",
            "(+ (put {} Num Num))",
            "(+ (put (put {} Num Num)))",
            "(+ (put (put {} Num Num)))",
            "(+ (put (put {} Num Num) Num))",
            "(+ (put (put {} Num Num) Num))",
            "(+ (put (put {} Num Num) Num))",
            "(+ (put (put {} Num Num) Num Num))",
            "(+ (put (put {} Num Num) Num Num))",
            "(+ (put (put {} Num Num) Num Num))",

            ////////////
            "(- (put Num))",
            "(- (put true))",
            "(- (put Num))",
            "(- (put (put {})))",
            "(- (put (put {} true)))",
            "(- (put (put {})))",
            "(- (put (put {} Num)))",
            "(- (put (put {} Num true) Num Num))",
            "(- (put (put {} Num true) true))",
            "(- (put (put {} Num Num) true))",
            "(- (put (put {} Num Num) Num true))",
            "(- (put (put {} true Num) Num))",
            "(- (put (put {} true Num) true true))",
        )

    // TODO next: chain operator takes dicts ab, bc and produces ac

    private val exs = basics + put

    override val examples: Examples = signedExamplesFromStrings(exs)
    override val oracle =
        CheckingOracle(
            mapOf(
                "Num" to "(i)",
                "true" to "(b)",
                "{}" to "(d a b)",
                "put" to "(-> (d k v) (-> k (-> v (d k v))))"
            )
                .mapValues { parseType(it.value) })
}
