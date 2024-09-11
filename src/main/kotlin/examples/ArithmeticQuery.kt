import bottomup.BottomUp
import sketchral.InputFactory
import sketchral.OutputParser
import sketchral.Result
import sketchral.withNegEx
import util.*
import java.io.File
import java.io.IOException
import java.util.concurrent.TimeUnit 



private val sumEx by lazy{
    mutableListOf<Example>(
        Example(listOf(1, 3), 4),
        Example(listOf(0, 3), 3)
    )
} 
private val diffEx by lazy{
    mutableListOf<Example>(
        Example(listOf(1, 3), -2), 
        Example(listOf(0, 1), 1), 
        Example(listOf(1,0), 1)
    )
} 
private val mulEx by lazy{
    mutableListOf<Example>(
        Example(listOf(2, 2), 4),
        Example(listOf(1, 0), 0),
        Example(listOf(0, 0), 0)  
    )
} 
private val maxEx by lazy{
    mutableListOf<Example>(
        Example(listOf(2, 5), 5),
        Example(listOf(3, 1), 3)
    )
} 
private val sumFunc = Func(null,Type(listOf(Int::class, Int::class), List::class), sumEx, mutableListOf<Example>())
private val diffFunc = Func(null,Type(listOf(Int::class, Int::class), List::class), diffEx, mutableListOf<Example>())
private val mulFunc =Func(null,Type(listOf(Int::class, Int::class), List::class), mulEx, mutableListOf<Example>())
private val maxFunc = Func(null,Type(listOf(Int::class, Int::class), List::class), maxEx, mutableListOf<Example>())
object ArithImpl : UPrimImpl {
    override fun len(x: Any): Int =
        when (x) {
            is Int -> x
            else -> throw UnsupportedOperationException("Length is not implemented for $x")
        }
}
private val funlist = listOf(sumFunc,diffFunc, mulFunc,maxFunc)
private val namelist = listOf("sum", "diff", "mul", "max")
val arithmeticquery by lazy {
    Query(funlist, ArithImpl)
}
val arithmeticTest by lazy{
    TestQuery(funlist,namelist,arithmeticquery, "./test_outputs/arithmetic/")
}
