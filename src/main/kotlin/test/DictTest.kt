package test

import enumgen.types.parseType
import util.CheckingOracle
import util.Query
import util.parseNewExamples

object DictTest {
    private val basics = listOf(
        "(+ 0)",
        "(+ 1)",
        "(+ tr)",
        "(+ Eib)",
        "(+ Ebi)",
        "(+ put)"
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
        ///////
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

    val examples = basics + put

    val query: Query = parseNewExamples(examples)
    val oracle = CheckingOracle(mapOf(
        "0" to "(i)",
        "1" to "(i)",
        "tr" to "(b)",
        "Eib" to "(d (i) (b))",
        "Ebi" to "(d (b) (i))",
        "put" to "(-> (d k v) (-> k (-> v (d k v))))"
    ).mapValues { parseType(it.value) })
}

//private val basics = mapOf(
//    "(+ 0)" to "(i)",
//    "(+ 1)" to "(i)",
//    "(+ tr)" to "(b)",
//    "(+ Eib)" to "(d (i) (b))",
//    "(+ Ebi)" to "(d (b) (i))",
//)
//private val put = mapOf(
//    "(+ (put Eib))" to "(-> (i) (-> (b) (d (i) (b))))",
//    "(+ (put Eib 0))" to "(-> (b) (d (i) (b)))",
//    "(+ (put Eib 1))" to "(-> (b) (d (i) (b)))",
//    "(+ (put Eib 0 tr))" to "(d (i) (b))",
//    "(+ (put (put Eib 0 tr)))" to "(-> (i) (-> (b) (d (i) (b))))",
//    "(+ (put (put Eib 0 tr) 0))" to "(-> (b) (d (i) (b)))",
//    "(+ (put (put Eib 0 tr) 0 tr))" to "(d (i) (b))",
//    "(+ (put (put Eib 0 tr) 1 tr))" to "(d (i) (b))",
//    ////////////
//    "(+ (put Ebi))" to "(-> (b) (-> (i) (d (b) (i))))",
//    "(+ (put Ebi tr))" to "(-> (i) (d (b) (i)))",
//    "(+ (put Ebi tr 0))" to "(d (b) (i))",
//    "(+ (put (put Ebi tr 0)))" to "(-> (b) (-> (i) (d (b) (i))))",
//    "(+ (put (put Ebi tr 0) tr))" to "(-> (i) (d (b) (i)))",
//    "(+ (put (put Ebi tr 0) tr 0))" to "(d (b) (i))",
//    "(+ (put (put Ebi tr 1) tr 0))" to "(d (b) (i))",
//)