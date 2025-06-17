package test

import query.Query
import query.parseExamples
import types.parseType
import util.CheckingOracle

object DictTest {
    private val basics = listOf(
        "(+ 0)",
        "(+ 1)",
        "(+ tr)",
        "(+ Eib)",
        "(+ Ebi)",
        "(+ Eii)",
        "(+ put)",
    )
    private val put = listOf(
        "(+ (put Eib))",
        "(+ (put Eib 0))",
        "(+ (put Eib 1))",
        "(+ (put Eib 0 tr))",
        "(+ (put (put Eib 0 tr)))",
        "(+ (put (put Eib 1 tr)))",
        "(+ (put (put Eib 0 tr) 0))",
        "(+ (put (put Eib 0 tr) 1))",
        "(+ (put (put Eib 1 tr) 1))",
        "(+ (put (put Eib 0 tr) 0 tr))",
        "(+ (put (put Eib 0 tr) 1 tr))",
        "(+ (put (put Eib 1 tr) 1 tr))",
        ////////////
        "(+ (put Ebi))",
        "(+ (put Ebi tr))",
        "(+ (put Ebi tr 0))",
        "(+ (put (put Ebi tr 0)))",
        "(+ (put (put Ebi tr 0) tr))",
        "(+ (put (put Ebi tr 0) tr 0))",
        "(+ (put (put Ebi tr 1) tr 0))",
        "(+ (put (put Ebi tr 1) tr))",
        "(+ (put (put Ebi tr 1) tr 1))",
        //////////
//        "(+ (put Ebb))",
//        "(+ (put Ebb tr))",
//        "(+ (put Ebb tr tr))",
//        "(+ (put (put Ebb tr tr)))",
//        "(+ (put (put Ebb tr tr) tr))",
//        "(+ (put (put Ebb tr tr) tr tr))",
//        //////////
        "(+ (put Eii))",
        "(+ (put Eii 0))",
        "(+ (put Eii 1))",
        "(+ (put Eii 0 1))",
        "(+ (put Eii 1 0))",
        "(+ (put Eii 1 1))",
        "(+ (put (put Eii 0 0)))",
        "(+ (put (put Eii 1 0)))",
        "(+ (put (put Eii 0 1) 0))",
        "(+ (put (put Eii 0 1) 1))",
        "(+ (put (put Eii 1 0) 1))",
        "(+ (put (put Eii 0 0) 0 1))",
        "(+ (put (put Eii 0 0) 1 0))",
        "(+ (put (put Eii 1 0) 1 1))",

        ////////////
        "(- (put 0))",
        "(- (put tr))",
        "(- (put 1))",
        "(- (put (put Ebi)))",
        "(- (put (put Ebi tr)))",
        "(- (put (put Eib)))",
        "(- (put (put Eib 0)))",
        "(- (put Ebi 0))",
        "(- (put Eib tr))",
        "(- (put Eib 0 0))",
        "(- (put Eib 0 1))",
        "(- (put Ebi tr tr))",
    )

    // TODO next: chain operator takes dicts ab, bc and produces ac

    val examples = basics + put

    val query: Query = parseExamples(examples)
    val oracle = CheckingOracle(mapOf(
        "0" to "(i)",
        "1" to "(i)",
        "tr" to "(b)",
        "Eib" to "(d (i) (b))",
        "Ebi" to "(d (b) (i))",
        "Eii" to "(d (i) (i))",
        "Ebb" to "(d (b) (b))",
        "put" to "(-> (d k v) (-> k (-> v (d k v))))"
    ).mapValues { parseType(it.value) })
}
