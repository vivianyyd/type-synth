import bottomup.BottomUp
import sketchral.InputFactory
import sketchral.OutputParser
import sketchral.Result
import sketchral.withNegEx
import util.*
import java.io.File
import java.io.IOException
import java.util.concurrent.TimeUnit 



private val subEx by lazy{
    mutableListOf<Example>(
        Example(listOf("cat", 0,1), "c"),
        Example(listOf("compute",0,7), "compute"),
    )
} 
private val concatEx by lazy{
    mutableListOf<Example>(
        Example(listOf("sub", "string"), "substring"),
        Example(listOf("", "concat"), "concat")
    )
} 
private val charEx by lazy{
    mutableListOf<Example>(
        Example(listOf("string", 0), "s"),
        Example(listOf("cat", 2), "t"),
        Example(listOf("course", 5), "e")
    )
} 
private val substituteEx by lazy{
    mutableListOf<Example>(
        Example(listOf("1 x-, 2 x-", "x-", "_"), "1 _, 2 _"),
        Example(listOf("1 x, 2 x", "x", "__"), "1 __, 2 __"),
        Example(listOf("1x, 2x", "x", "___"), "1___, 2___"),
        Example(listOf("cat", "dog", "fish"), "cat")
    )
} 
private val substitute1Ex by lazy{
    mutableListOf<Example>(
        Example(listOf("first phrase, second phrase, third phrase", "phrase", "_"), "first _, second phrase, third phrase"),
        Example(listOf("first phrase, second phrase, third phrase", "phrase", "__________"), "first__________, second phrase, third phrase"),
        Example(listOf("cat", "dog", "fish"), "cat")
    )
} 
private val selectEx by lazy{
    mutableListOf<Example>(
        Example(listOf(true, "first111", "second"), "first111"),
        Example(listOf(false, "true", ""),"")
    )
} 
private val caseEx by lazy{
    mutableListOf<Example>(
        Example(listOf("word"), "WORD"),
        Example(listOf(""),"")
    )
} 
private val substringFunc = Func(null,Type(listOf(String::class, Int::class, Int::class), String::class), subEx, mutableListOf<Example>())
private val concatFunc = Func(null,Type(listOf(String::class, String::class), String::class), concatEx, mutableListOf<Example>())
//private val charFunc=Func(null,Type(listOf(String::class, Int::class), String::class), charEx, mutableListOf<Example>())
private val caseFunc=Func(null,Type(listOf(String::class), String::class), caseEx, mutableListOf<Example>())
private val substituteFunc=Func(null,Type(listOf(String::class, String::class, String::class), String::class), substituteEx, mutableListOf<Example>())
private val substitute1Func=Func(null,Type(listOf(String::class, String::class, String::class), String::class), substitute1Ex, mutableListOf<Example>())
private val selectFunc=Func(null,Type(listOf(Boolean::class, String::class, String::class), String::class), selectEx, mutableListOf<Example>())

object StringImpl : UPrimImpl {
    override fun len(x: Any): Int =
        when (x) {
            is String -> x.length
            else -> throw UnsupportedOperationException("Length is not implemented for $x")
        }
}
private val funlist = listOf<Func>(substringFunc, concatFunc, substituteFunc, substitute1Func, selectFunc, caseFunc)
private val namelist = listOf<String>("substring", "concat",  "substitute", "subFirst", "select", "uppercase")
val stringquery by lazy {
    Query(funlist, StringImpl)
}
val stringTest by lazy{
    TestQuery(funlist,namelist,stringquery, "./test_outputs/string/")
}
