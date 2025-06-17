package util

import constraints.LabelConstraintGenerator
import std.SymTypeDFlat
import std.Var

class CVCParser(input: String, constrGen: LabelConstraintGenerator) {
    val paramSets: Map<ParameterNode, Set<Int>>
    val sizes: Map<SymTypeDFlat, Int>
    val varDummies: Map<Var, Int>

    init {
        val (paramSetsE, rest) = map(input).entries.partition { it.key.startsWith('p') }
        val (sizesE, varsE) = rest.partition { it.key.startsWith("size") }

        paramSets = paramSetsE.associate { constrGen.pyParamToNode(it.key) to parseSet(it.value) }
        sizes = sizesE.associate { constrGen.pySizeToL(it.key) to it.value.toInt() }
        varDummies = varsE.associate { Var(constrGen.pyVarToIds(it.key)) to it.value.toInt() }

    }

    fun print() {
        println(paramSets)
        println(sizes)
        println(varDummies)
    }
    
    private fun map(input: String): Map<String, String> =
        split(input).map { it.split("=") }.filter { it.size == 2 }.map { it[0].trim() to it[1].trim() }.toMap()

    private fun split(input: String): List<String> {
        val trimmed = input.trim().removePrefix("[").removeSuffix("]")
        val result = mutableListOf<String>()
        val sb = StringBuilder()
        var depth = 0
        for (c in trimmed.filter { !it.isWhitespace() }) {
            when (c) {
                ',' -> {
                    if (depth == 0) {
                        result.add(sb.toString().trim())
                        sb.clear()
                    } else sb.append(c)
                }
                '(' -> {
                    depth++
                    sb.append(c)
                }
                ')' -> {
                    depth--
                    sb.append(c)
                }
                else -> sb.append(c)
            }
        }
        if (sb.isNotEmpty()) result.add(sb.toString().trim())
        return result
    }

    private fun parseSet(expr: String): Set<Int> {
        fun splitTopLevelComma(s: String): Pair<String, String> {
            var depth = 0
            for (i in s.indices) {
                when (s[i]) {
                    '(' -> depth++
                    ')' -> depth--
                    ',' -> if (depth == 0) {
                        return s.substring(0, i).trim() to s.substring(i + 1).trim()
                    }
                }
            }
            error("Could not find top-level comma in: $s")
        }

        val trimmed = expr.trim()
        return when {
            trimmed.startsWith("Empty(") -> setOf()
            trimmed.startsWith("Singleton(") -> {
                val inner = trimmed.removePrefix("Singleton(").removeSuffix(")").trim()
                setOf(inner.toInt())
            }
            trimmed.startsWith("SetUnion(") -> {
                // Find the comma separating the two arguments at the top level
                val inner = trimmed.removePrefix("SetUnion(").removeSuffix(")")
                val (leftStr, rightStr) = splitTopLevelComma(inner)
                parseSet(leftStr) union parseSet(rightStr)
            }
            else -> error("Unknown expression: $trimmed")
        }
    }
}
