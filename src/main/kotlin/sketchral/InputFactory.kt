package sketchral

import util.Example
import util.Func
import util.Query
import util.U

fun InputFactory.withNegEx(neg: Example): InputFactory {
    val newFunc = function.withNegExample(neg)
    return InputFactory(newFunc, query.replace(function, newFunc))
}

class InputFactory(val function: Func, val query: Query) {
    private val numAtom = 1  // TODO add flag later
    private val minimizeTerms = false  // TODO add commandline flag later
    private val numInputs = function.type.inputs.size
    private val argToDummy = mutableMapOf<Any, Int>()
    val dummyToArg = mutableMapOf<Int, Any>()
    private val outputDummies: Set<Int>
    private val paramsWithLen =
        (0..numInputs).filter { (if (it == numInputs) -1 else it) !in function.argsWithUndefinedLength }

    init {
    for (example in function.posExamples) 
    {
        println(example)}  
        // Make dummy values for examples
        val typeList = function.type.inputs + listOf(function.type.output)
        function.examples.flatMap { (it.inputs + listOf(it.output)) }.toSet().forEachIndexed { i, arg ->
            argToDummy[arg] = i
            dummyToArg[i] = arg
        }
        outputDummies = function.examples.mapNotNull { argToDummy[it.output] }.toSet()

    }

    private fun paramToName(param: Int) = if (param == numInputs) "o" else "x$param"
    private val argsRefDefn = (0..numInputs).joinToString(separator = ", ") { "ref int ${paramToName(it)}" }
    private val argsDefn = (0..numInputs).joinToString(separator = ", ") { "int ${paramToName(it)}" }
    private val argsCall = (0..numInputs).joinToString(separator = ", ") { paramToName(it) }

    /**
     * Spyro generates code for positive examples which looks like:
     *      int o = 0;
     *      max2(-12, -2, o);
     *      boolean out;
     *      property(-12, -2, o, out);
     *      assert out;
     * For the same example, we write:
     *      boolean out;
     *      property(-12, -2, -1, out);
     *      assert out;
     * Spyro generates code for negative examples which looks like:
     *      boolean out;
     *      property(-31, -30, -30, out);
     *      assert !out;
     * For the same example, we generate the same code.
     */
    private fun sketchEx(ex: Example, negative: Boolean): String {
        val lines = mutableListOf<String>()
        lines.add("\tboolean out;")

        // Declare and define values
        lines.addAll(ex.args.mapIndexed { i, arg ->
            "int ${paramToName(i)} = ${argToDummy[arg]};"
        })

        lines.add("property($argsCall, out);")
        lines.add("assert ${if (negative) "!" else ""}out;")
        return lines.joinToString(separator = "\n\t")
    }

    private fun posExamples(): String {
        val sk = StringBuilder()
        function.posExamples.forEachIndexed { i, ex ->
            sk.append("harness void positive_example_$i () {\n${sketchEx(ex, false)}\n}\n")
        }
        return sk.toString()
    }

    private fun negExamplesSynth(negMay: Examples): String {
        val sk = StringBuilder()
        (negMay + function.negExamples).forEachIndexed { i, ex ->
            sk.append("\nharness void negative_example_$i () {\n${sketchEx(ex, true)}\n}\n\n")
        }
        return sk.toString()
    }

    private fun propertyCode(maxsat: Boolean = false): String {
        fun propertyGenCode(n: Int) = (0 until n).joinToString(separator = " || ") { "atom_$it" }

        val atomGen = "U_gen(${argsCall}, n)"
        val sk = StringBuilder()

        // Emit generator for property
        sk.append("generator boolean property_gen(${argsDefn}) {\n")
        sk.append("\tif (??) { return false; }\n")
        sk.append("\tint n = ??;\n")
        if (minimizeTerms && !maxsat) {
            sk.append("\tint t = ??;\n")
            for (i in 0 until numAtom) {
                val propertyGen = propertyGenCode(i + 1)
                sk.append("\tboolean atom_$i = ${atomGen};\n")
                sk.append("\tminimize(n);\n")
                sk.append("\tif (t == ${i + 1}) { return ${propertyGen}; }\n")
            }
            sk.append("\tminimize(t);\n")
        } else {
            for (i in 0 until numAtom) {
                sk.append("\tboolean atom_${i} = ${atomGen};\n")
            }
            val propertyGen = propertyGenCode(numAtom)
            sk.append("\tminimize(n);\n")
            sk.append("\treturn ${propertyGen};\n")
        }
        sk.append("}\n")

        // Set property to be the result of calling generator
        sk.append("void property(${argsDefn}, ref boolean out) {\n")
        sk.append("\tout = property_gen(${argsCall});\n")
        sk.append("}\n")
        return sk.toString()
    }

    private val setup by lazy {
        // Declare length function
        val ld = mutableListOf("int length(int x) {")
        function.examples.flatMap { it.args.filterIndexed { i, _ -> i in paramsWithLen } }.toSet().forEach { arg ->
            ld.add("if (x == ${argToDummy[arg]}) { return ${query.lens[arg]}; }")
        }
        ld.add("assert false;")
        ld.joinToString(separator = "\n\t", postfix = "\n}\n")
    }

    fun synthInput(negMay: Examples, lams: Lambdas): String {
        val sk = StringBuilder()
        sk.append(setup)
        sk.append(uGrammar)
        sk.append(lamFunctions(lams))
        sk.append("// -------------------- Begin examples ------------------------\n")
        sk.append(posExamples())
        sk.append(negExamplesSynth(negMay))
        sk.append("// -------------------- End examples ------------------------\n\n")
        sk.append(propertyCode())
        return sk.toString()
    }

    fun maxsatInput(pos: Examples, negMust: Examples, negMay: Examples, lams: Lambdas): String {
        TODO()
    }

    fun soundnessInput(phi: U, lams: Lambdas): String {
        TODO()
    }

    private fun obtainedPropertyCode(phi: String): String {
        return "void obtained_property($argsDefn, ref boolean out) {\n\tout = ${phi}\n}\n\n"
    }

    private fun prevPropertyCode(i: Int, phi: String): String {
        return "void prev_property_$i($argsDefn, ref boolean out) {\n\tout = ${phi}\n}\n\n"
    }

    private fun propertyConjCode(phiList: List<String>): String {
        val sb = StringBuilder()
        phiList.forEachIndexed { i, phi -> sb.append("${prevPropertyCode(i, phi)}\n") }

        val block = mutableListOf("void property_conj($argsDefn, ref boolean out) {")
        for (i in phiList.indices) {
            block.add("boolean out_$i;")
            block.add("prev_property_$i($argsCall, out_$i);")
        }
        if (phiList.isEmpty()) block.add("out = true;")
        else {
            block.add("out = ${(phiList.indices).joinToString(separator = " && ") { "out_$it" }};")
        }
        sb.append(block.joinToString(separator = "\n\t", postfix = "\n"))
        sb.append("}\n")
        return sb.toString()
    }

    private val getExample by lazy {
        val code = mutableListOf("// Returns the ith argument of the tth example.")
        code.add("int get_ex(int t, int i) {")
        function.posExamples.forEachIndexed { t, ex ->
            ex.args.forEachIndexed { i, arg ->
                code.add("if (t == $t && i == $i) { return ${argToDummy[arg]}; }")
            }
        }
        code.add("assert false;")
        code.joinToString(separator = "\n\t", postfix = "\n}\n")
    }

    private val dummyOutput by lazy {
        // TODO we can actually do everything in the query that's the same type as the output. that includes inputs of
        //  the correct type and inside examples for other functions
        val code = mutableListOf("generator int dummy_out() {")
        code.add("int t = ??;")
        outputDummies.forEachIndexed { i, v -> code.add("if (t == $i) { return $v; }") }
        code.add("assert false;")
        code.joinToString(separator = "\n\t", postfix = "\n}\n")
    }

    private val genNegativeExample by lazy {
        val code = mutableListOf("generator void negative_example_gen($argsRefDefn){")
        code.add("int t = ??;")
        // Select a preexisting combination of inputs
        (0 until numInputs).forEach {
            code.add("${paramToName(it)} = get_ex(t, $it);")
        }
        // Select an output which is not the real one
        code.add("o = dummy_out();")
        code.add("int real_out = get_ex(t, $numInputs);")
        code.add("assert o != real_out;")
        code.joinToString(separator = "\n\t", postfix = "\n}\n")
    }

    private val negativeExample by lazy {
        val code = mutableListOf("void negative_example($argsRefDefn){")
        code.add("negative_example_gen($argsCall);")
        code.joinToString(separator = "\n\t", postfix = "\n}\n")
    }

    private fun precisionCode(): String {
        val code = mutableListOf("harness void precision() {")
        // Construct negative example
        /* Spyro doesn't directly synthesize a negative example; they just call generators to get values of the
           correct type. As a result, they need to do checkSoundness after this step since they might synth a
           "counterexample" that's actually positive, resulting in an unsound property. But we just directly synthesize
           an example which is certainly negative, so we can skip that step! */
        (0 ..numInputs).forEach { code.add("int ${paramToName(it)} = 0;") }
        code.add("negative_example($argsCall);")
        // Previous property is true on our counterexample
        code += "boolean out_1;"
        code += "obtained_property($argsCall, out_1);"
        code += "assert out_1;\n"
        // Our counterexample is new, that is, no prev phis reject it
        code += "boolean out_2;"
        code += "property_conj($argsCall, out_2);"
        code += "assert out_2;\n"
        // We have a new property that rejects it, so it is strictly more precise
        code += "boolean out_3;"
        code += "property($argsCall, out_3);"
        code += "assert !out_3;"
        return code.joinToString(separator = "\n\t", postfix = "\n}\n")
    }

    fun precisionInput(
        phi: String,
        phiList: List<String>,
        negMay: Examples,
        lams: Lambdas
    ): String {
        val sk = StringBuilder()
        sk.append(setup)
        sk.append(uGrammar)
        sk.append(genNegativeExample)
        sk.append(negativeExample)
        sk.append(getExample)
        sk.append(dummyOutput)
        sk.append(lamFunctions(lams))
        sk.append("// -------------------- Begin examples ------------------------\n")
        sk.append(posExamples())
        sk.append(negExamplesSynth(negMay))
        sk.append("// -------------------- End examples ------------------------\n\n")
        sk.append(propertyCode())
        sk.append(obtainedPropertyCode(phi))
        sk.append(propertyConjCode(phiList))
        sk.append(precisionCode())
        return sk.toString()
    }

    /**
     * Generator for elements of U
     */
    private val uGrammar by lazy {
        // I guess we don't need &&,|| since || is part of propertygen and && is built
        // into synthall. and we don't need not, since each compare has a not
        val sb = StringBuilder("// -------------------- Grammar of properties ------------------------\n")

        // The toplevel predicate non-terminal
        val uGen = mutableListOf("generator boolean U_gen($argsDefn, int n) {")
        uGen.add("if (n > 0) {")
        uGen.add("\tint e1 = U_gen_expr($argsCall, n - 1);")
        uGen.add("\tint e2 = U_gen_expr($argsCall, n - 1);")
        uGen.add("\treturn U_gen_cmp(e1, e2, n - 1);")
        uGen.add("}")
        uGen.add("assert false;")
        sb.append(uGen.joinToString(separator = "\n\t"))
        sb.append("\n}\n")

        val compareGen = mutableListOf("generator boolean U_gen_cmp(int x, int y, int n) {")
        compareGen.add("if (n > 0) {")
        compareGen.add("\tint t = ??;")
        compareGen.add("\tif (t == 0) { return x == y; }")
        compareGen.add("\tif (t == 1) { return x <= y; }")
        compareGen.add("\tif (t == 2) { return x >= y; }")
        compareGen.add("\tif (t == 3) { return x < y; }")
        compareGen.add("\tif (t == 4) { return x > y; }")
        compareGen.add("\treturn x != y;")
        compareGen.add("}")
        compareGen.add("assert false;")
        sb.append(compareGen.joinToString(separator = "\n\t"))
        sb.append("\n}\n")

        // Integer expressions
        val eGen = mutableListOf("generator int U_gen_expr($argsDefn, int n) {")
        eGen.add("if (n > 0) {")
        eGen.add("\tint t = ??;")
        eGen.add("\tif (t == 0) { return 0; }")
        eGen.add("\tif (t == 1) { return 1; }")
        paramsWithLen.forEachIndexed { tOffset, param ->
            eGen.add("\tif (t == ${tOffset + 2}) { return length(${if (param == numInputs) "o" else "x$param"}); }")
        }
        eGen.add("\tint e1 = U_gen_expr($argsCall, n - 1);")
        eGen.add("\tint e2 = U_gen_expr($argsCall, n - 1);")
        eGen.add("\treturn U_gen_op(e1, e2, n - 1);")
        eGen.add("}")
        eGen.add("assert false;")
        sb.append(eGen.joinToString(separator = "\n\t"))
        sb.append("\n}\n")

        val opGen = mutableListOf("generator int U_gen_op(int x, int y, int n) {")
        opGen.add("if (n > 0) {")
        opGen.add("\tint t = ??;")
        opGen.add("\tif (t == 0) { return x + y; }")
        opGen.add("\tif (t == 1) { return x * y; }")
        opGen.add("\treturn x - y;")
        opGen.add("}")
        opGen.add("assert false;")
        sb.append(opGen.joinToString(separator = "\n\t"))
        sb.append("\n}\n")

        sb.append("// -------------------- End grammar of properties ------------------------\n\n")
        sb.toString()
    }

    /** Gonna keep this til we understand it */
    private fun lamFunctions(lams: Lambdas) = lams.values.joinToString(postfix = "\n", separator = "\n")
}
