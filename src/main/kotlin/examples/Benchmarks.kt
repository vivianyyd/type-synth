import bottomup.BottomUp
import sketchral.InputFactory
import sketchral.OutputParser
import sketchral.Result
import sketchral.withNegEx
import util.*
import java.io.File
import java.io.IOException
import java.util.concurrent.TimeUnit 
import java.nio.file.Files
import java.nio.file.Paths

data class TestQuery(val  functions:List<Func>, val names:List<String> , val query:Query,val strpath:String){
    val map: Map<String, Func>
    val path:String
    init{

        path = strpath

        Files.createDirectories(Paths.get(path))
      map = mutableMapOf<String, Func>()
      for(i in 0..names.size-1){
        map.put(names.get(i), functions.get(i))
      }
    } 
    fun runTest(){
        for(key in map.keys){
            println(System.currentTimeMillis())
        var file: String = path+"/"+key+".txt"
        var func = map.get(key)!!
        var ifac = InputFactory(func, query)
        val synth = callSketch(ifac.synthInput(listOf(), mapOf()))
        var res = OutputParser(synth, ifac).parseProperty()
        if (res !is Result.Ok) return;
        var phi = res.value
        //////this is where we need to put in the redirect of output and send it to path
        File(file).writeText("\nInitial synthesized property: $phi")
        while(true){
            val precision = callSketch(ifac.precisionInput(phi, listOf(), listOf(), mapOf()))
            val op = OutputParser(precision, ifac)
            val result = op.parseProperty()
            for(input in func.posExamples){
                File(file).appendText("\nExample:     "+input)
            }
            if (result is Result.Ok) {
                phi = result.value
                File(file).appendText("\nProperty with increased precision: $phi")
                ifac = ifac.withNegEx(op.parseNegExPrecision())
            }
            else break
        }
        println(System.currentTimeMillis())
        }
    } 
}