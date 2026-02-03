package products

import dependencyanalysis.*
import products.concreteenumerator.ConcreteEnumerator
import products.concreteenumerator.ConcreteNode
import products.constraints.LabelConstraintGenerator
import products.sta.SymTypeABuilder
import products.stc.*
import query.Query
import test.Test
import util.*

/** Infrastructure for the old implementation. */
data class ConfigForOld(
    val test: Test,
    val runCVC: Boolean,
    val maxDepth: Int,
    val writeIR: Boolean = true
) : Config {
    override fun toString(): String =
        listOf(test.name, "Running CVC: $runCVC", "Max depth: $maxDepth")
            .joinToString(separator = "\n", postfix = "\n=====\n")
}

fun run(config: ConfigForOld, logger: Logger) {
    val (query, oracle) = config.test.pair()
    if (config.writeIR) clearOutlines()
    if (config.runCVC) clearCVC()

    val outlines =
        if (config.writeIR)
            SymTypeCEnumerator(query, SymTypeABuilder(query).make, oracle).enumerateAll()
        else readIntermediateOutlines().map { it.second }
    if (config.writeIR)
        outlines.forEachIndexed { i, it ->
            writeIntermediateOutline("${it.outline.toSExpr()}", "$i")
        }

    println("Starting dependency analysis")
    val aritiesToDeps = aritiesToDeps(query, oracle, outlines)
    //    vizDeps(listOf("put", "chain"), aritiesToDeps)

    val outlinesPruned =
        outlines.filter {
            val deps = aritiesToDeps[it.arities]!!
            val constrs = constraintsForOldPipeline(it, deps)
            it.parameterToType.all { (p, t) ->
                val c = constrs[p.f]?.get(p.i)
                when (c) {
                    ContainsNoVariables -> t !is Var
                    is ContainsOnly -> (t !is Var) || (t.vId == c.vId && t.tId == c.tId)
                    is MustContainVariables ->
                        (t !is Var) ||
                                (c.vars.size == 1 &&
                                        t.vId == c.vars[0].first &&
                                        t.tId == c.vars[0].second)
                    null -> true
                }
            }
        }

    println(outlinesPruned.joinToString(separator = "\n") { it.outline.toString() })
    println("Pruned outlines: ${outlinesPruned.size}")

    println("Searching for label sizes with CVC")
    val candidateToLabelSizes = assignLabelSizes(outlinesPruned, aritiesToDeps, config.runCVC)

    println("Search seeds:")
    candidateToLabelSizes.map { (candidate, lSizes) ->
        print("$candidate")
        printSearchSeed(lSizes, outlinesPruned[candidate])
    }

    println("Enumerating")
    val OK = mutableListOf<Map<String, ConcreteNode>>()

    val enumerators =
        candidateToLabelSizes.map { (candidate, lSizes) ->
            println("\n\n")
            printSearchSeed(lSizes, outlinesPruned[candidate])
            ConcreteEnumerator(
                query,
                outlinesPruned[candidate],
                lSizes,
                aritiesToDeps[outlinesPruned[candidate].arities]!!,
                oracle,
                logger
            )
        }
    for (i in 1..config.maxDepth) {
        if (OK.isNotEmpty()) break
        println("Depth $i")
        enumerators.forEach { OK.addAll(it.step()) }
    }

    logger.finish()
    println("Solutions:")
    OK.forEach { println(it.toList().joinToString(separator = "\n", postfix = "\n---\n")) }
    println("${OK.size} satisfying contexts")
}

// No need for dep analysis for every candidate, just every arrow skeleton (unique mappings of name
// to arity)
private fun aritiesToDeps(
    query: Query,
    oracle: Oracle,
    outlines: List<Projection>
): Map<Map<String, Int>, ArrowDependencyAnalysis> =
    outlines.map { it.arities }.toSet().associateWith { ArrowDependencyAnalysis(query, it, oracle) }

private fun vizDeps(
    components: List<String>,
    aritiesToDeps: Map<Map<String, Int>, ArrowDependencyAnalysis>
) = aritiesToDeps.entries.mapIndexed { i, it -> components.map { f -> viz(f, it.value, "$f$i") } }

private fun assignLabelSizes(
    outlines: List<Projection>,
    aritiesToDeps: Map<Map<String, Int>, ArrowDependencyAnalysis>,
    runCVC: Boolean
): Map<Int, Map<L, Int>> {
    val cvcGens =
        outlines.withIndex().associate { (i, outline) ->
            i to LabelConstraintGenerator(outline, aritiesToDeps[outline.arities]!!)
        }
    if (runCVC) {
        cvcGens.forEach { (i, gen) -> callCVC(gen.initialQuery(), "$i") }
        return readInitialCVCresults().associate { (i, contents) ->
            i to minLabelSizes(i, contents, cvcGens[i]!!)
        }
    } else {
        return readSmallestCVCresults().associate { (i, contents) ->
            i to CVCParser(contents).sizes.mapKeys { cvcGens[i]!!.pySizeToL(it.key) }
        }
    }
}

private fun minLabelSizes(
    testId: Int,
    prevSol: String,
    cvcGenerator: LabelConstraintGenerator
): Map<L, Int> {
    var counter = 0
    var previousSolution = prevSol
    var lastSuccessful = -1
    do {
        println("Getting smaller CVC results")
        val parser = CVCParser(previousSolution)
        val testName = "$testId-smaller${counter++}"
        val cont =
            if (parser.sizes
                    .isNotEmpty()
            ) // TODO FIXME if the flag is off we don't read previous results
            // properly
                callCVC(
                    cvcGenerator.smallerQuery(
                        parser.sizes.mapKeys { cvcGenerator.pySizeToL(it.key) }),
                    testName
                )
            else false
        if (cont) {
            lastSuccessful = counter - 1
            previousSolution = readCVC(testName)!!
        }
    } while (cont)
    val finalSuccessfulOutput =
        if (lastSuccessful == -1) "$testId" else "$testId-smaller$lastSuccessful"
    return CVCParser(readCVC(finalSuccessfulOutput)!!).sizes.mapKeys {
        cvcGenerator.pySizeToL(it.key)
    }
}

private fun printSearchSeed(labelSizes: Map<L, Int>, outline: Projection) {
    fun SymTypeC.toStringWithSizes(): String =
        when (this) {
            is L -> "$this[${List(labelSizes[this]!!) { "_" }.joinToString(separator = ",")}]"
            is Var -> this.toString()
            is F ->
                "${if (left is F) "(${left.toStringWithSizes()})" else "${left.toStringWithSizes()}"} -> ${rite.toStringWithSizes()}"
        }
    println(
        outline.outline.entries.joinToString(prefix = "{", postfix = "}", separator = ", ") { (component, type) ->
            "$component: ${type.toStringWithSizes()}"
        })
}

fun <T> Iterable<T>.pr() = this.joinToString(separator = "\n")
