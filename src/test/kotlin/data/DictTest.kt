package data

import products.types.parseType
import query.AbstractQuery
import query.Examples
import util.CheckingOracle
import util.io.signedExamplesFromStrings

object DictTest : AbstractQuery() {
    private val basics =
        listOf(
            "(+ Num)",
            "(+ Num)",
            "(+ true)",
            "(+ Eib)",
            "(+ Ebi)",
            "(+ Eii)",
            "(+ put)",
        )
    private val put =
        listOf(
            "(+ (put Eib))",
            "(+ (put Eib Num))",
            "(+ (put Eib Num))",
            "(+ (put Eib Num true))",
            "(+ (put (put Eib Num true)))",
            "(+ (put (put Eib Num true)))",
            "(+ (put (put Eib Num true) Num))",
            "(+ (put (put Eib Num true) Num))",
            "(+ (put (put Eib Num true) Num))",
            "(+ (put (put Eib Num true) Num true))",
            "(+ (put (put Eib Num true) Num true))",
            "(+ (put (put Eib Num true) Num true))",
            ////////////
            "(+ (put Ebi))",
            "(+ (put Ebi true))",
            "(+ (put Ebi true Num))",
            "(+ (put (put Ebi true Num)))",
            "(+ (put (put Ebi true Num) true))",
            "(+ (put (put Ebi true Num) true Num))",
            "(+ (put (put Ebi true Num) true Num))",
            "(+ (put (put Ebi true Num) true))",
            "(+ (put (put Ebi true Num) true Num))",
            //////////
            //        "(+ (put Ebb))",
            //        "(+ (put Ebb true))",
            //        "(+ (put Ebb true true))",
            //        "(+ (put (put Ebb true true)))",
            //        "(+ (put (put Ebb true true) true))",
            //        "(+ (put (put Ebb true true) true true))",
            //        //////////
            "(+ (put Eii))",
            "(+ (put Eii Num))",
            "(+ (put Eii Num))",
            "(+ (put Eii Num Num))",
            "(+ (put Eii Num Num))",
            "(+ (put Eii Num Num))",
            "(+ (put (put Eii Num Num)))",
            "(+ (put (put Eii Num Num)))",
            "(+ (put (put Eii Num Num) Num))",
            "(+ (put (put Eii Num Num) Num))",
            "(+ (put (put Eii Num Num) Num))",
            "(+ (put (put Eii Num Num) Num Num))",
            "(+ (put (put Eii Num Num) Num Num))",
            "(+ (put (put Eii Num Num) Num Num))",

            ////////////
            "(- (put Num))",
            "(- (put true))",
            "(- (put Num))",
            "(- (put (put Ebi)))",
            "(- (put (put Ebi true)))",
            "(- (put (put Eib)))",
            "(- (put (put Eib Num)))",
            "(- (put Ebi Num))",
            "(- (put Eib true))",
            "(- (put Eib Num Num))",
            "(- (put Eib Num Num))",
            "(- (put Ebi true true))",
            "(- (put Eii (put Eii Num Num)))"
        )

    private val exs = basics + put

    override val examples: Examples = signedExamplesFromStrings(exs)
    override val oracle =
        CheckingOracle(
            mapOf(
                "Num" to "(i)",
                "true" to "(b)",
                "Eib" to "(d (i) (b))",
                "Ebi" to "(d (b) (i))",
                "Eii" to "(d (i) (i))",
                "Ebb" to "(d (b) (b))",
                "put" to "(-> (d k v) (-> k (-> v (d k v))))"
            )
                .mapValues { parseType(it.value) })
}
