package bottomup

import util.*
import kotlin.reflect.KClass

interface Value

data class IntValue(val value: Int) : Value

data class BooleanValue(val value: Boolean) : Value

// TODO improve types for EvaluationResult/Value/etc

typealias TypeSize = Pair<KClass<*>, Int>

/** A mapping representing the result of evaluating some predicate for each example. */
typealias EvaluationResult = Map<Example, Value>

class BottomUp(private val query: Query) {
    private val properties: MutableMap<Func, UBoolean?> = mutableMapOf()

    fun property(function: Func, bound: Int = 8): UBoolean? {
        assert(function in query.functions)
        if (function in properties) return properties[function]
        return enumerate(function, bound)
    }

    fun enumerate(function: Func, bound: Int): UBoolean? {
        enumerateWithValues(function, bound).forEach { (node, evalResult) ->
            if (function.posExamples.all { (evalResult[it] as BooleanValue).value } &&
                function.negExamples.all { !(evalResult[it] as BooleanValue).value }) {
                return node
            }
        }
        return null
    }

    /** Just like [enumerate], but also yields the result of evaluating the yielded node in all environments as
    specified by the examples in [query]. Only yields booleans. */
    private fun enumerateWithValues(function: Func, bound: Int) = iterator {
        val typeSizeToExpr: MutableMap<TypeSize, MutableList<Pair<U, EvaluationResult>>> = mutableMapOf()
        val valuesToExpr: MutableMap<EvaluationResult, U> = mutableMapOf()

        // Some literals
        (0..1).forEach { literal ->
            val nodeAndEvaluated = Pair(ULiteral(literal), function.examples.associateWith { IntValue(literal) })
            typeSizeToExpr.addMulti(
                Pair(Int::class, 1),
                nodeAndEvaluated
            )
        }
        // The lengths of all parameters
        val lenTerminals =
            ((-1 until function.type.inputs.size)).filter { it !in function.argsWithUndefinedLength }.map { ULen(it) }
        val lenNodes = mutableListOf<Pair<U, EvaluationResult>>()
        for (lenNode in lenTerminals) {
            val evaluated = lenNode.evaluate(function, query.uImpl)
            if (evaluated in valuesToExpr) continue
            valuesToExpr[evaluated] = lenNode
            typeSizeToExpr.addMulti(
                Pair(Int::class, 1),
                Pair(lenNode, evaluated)
            )
            lenNodes.add(Pair(lenNode, evaluated))
        }

        /** Just here to reduce some code duplication. */
        fun generateAndStore(
            function: Func,
            numChildren: Int,
            makeNode: (List<Pair<U, EvaluationResult>>) -> U,
            childType: KClass<*>,
            returnType: KClass<*>,
            size: Int
        ) = iterator {
            for (childPartitions in intPartitions(size - 1 - numChildren, numChildren)) {
                val candidates = mutableListOf<List<Pair<U, EvaluationResult>>>()
                childPartitions.forEach { childMinusOne ->
                    typeSizeToExpr[Pair(childType, childMinusOne + 1)]?.let { candidates.add(it) }
                }
                if (candidates.size != numChildren) {
                    continue
                }  // we failed to find candidates for all children, so this partition won't work
                for (candidateArgs in product(candidates.first(), candidates.last())) {
                    val node = makeNode(candidateArgs)
                    val evaluated =
                        node.evaluateFromCachedChildren(function, query.uImpl, candidateArgs.map { it.second })
                    if (evaluated in valuesToExpr) continue
                    valuesToExpr[evaluated] = node
                    typeSizeToExpr.addMulti(Pair(returnType, size), Pair(node, evaluated))
                    yield(Pair(node, evaluated))
                }
            }
        }

        for (possSize in 2..bound) {
            IntOp.values().forEach { op ->
                generateAndStore(
                    function,
                    2,
                    makeNode = { args -> UOp(op, args.first().first as UInt, args.last().first as UInt) },
                    childType = Int::class,
                    returnType = Int::class,
                    size = possSize
                ).forEach { }
            }
            Cmp.values().forEach { cmp ->
                generateAndStore(
                    function,
                    2,
                    makeNode = { args -> UCmp(cmp, args.first().first as UInt, args.last().first as UInt) },
                    childType = Int::class,
                    returnType = Boolean::class,
                    size = possSize
                ).forEach { yield(it as Pair<UBoolean, EvaluationResult>) }
            }
            BoolOp.values().forEach { op ->
                when (op) {
                    BoolOp.AND, BoolOp.OR -> generateAndStore(
                        function,
                        2,
                        makeNode = { args -> UBop(op, args.first().first as UBoolean, args.last().first as UBoolean) },
                        Boolean::class,
                        Boolean::class,
                        possSize
                    ).forEach { yield(it as Pair<UBoolean, EvaluationResult>) }
                    BoolOp.NOT -> generateAndStore(
                        function,
                        1,
                        makeNode = { args -> UBop(op, args.first().first as UBoolean) },
                        Boolean::class,
                        Boolean::class,
                        possSize
                    ).forEach { yield(it as Pair<UBoolean, EvaluationResult>) }
                }
            }
        }
    }


    private fun <K, V> MutableMap<K, MutableList<V>>.addMulti(key: K, value: V) {
        if (key in this) {
            this[key]!!.add(value)
        } else {
            this[key] = mutableListOf(value)
        }
    }

    private fun intPartitions(target: Int, numParts: Int): List<List<Int>> {
        if (target < 0) return listOf()
        if (numParts == 1) return listOf(listOf(target))
        val parts = mutableListOf<List<Int>>()
        for (x1 in 0..target) {
            for (x2s in intPartitions(target - x1, numParts - 1)) {
                parts.add(listOf(x1) + x2s)
            }
        }
        return parts
    }

    private fun <T> product(a: List<T>, b: List<T>): List<List<T>> {
        val result = mutableListOf<List<T>>()
        a.forEach { ai ->
            b.forEach { bi ->
                result.add(listOf(ai, bi))
            }
        }
        return result
    }
}
