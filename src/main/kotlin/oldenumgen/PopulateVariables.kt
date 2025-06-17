package oldenumgen

import types.*
import types.Function

/** Assume the type has only Variables of the same name. Replace those and child holes with various paritionings
 * into at most [cap] variables
 *
 * pure function
 * */
fun Assignment.populateVariablesPartitionBlowup(nullary: Map<String, Boolean>, cap: Int): Set<Assignment> {
    val noNullary = this.filterKeys { !nullary[it]!! }
    val spots = noNullary.values.fold(0) { a, t -> a + t.recursiveNumVars() + t.recursiveNumChildHoles() }
    val partitions = partitionList((1..spots).toList(), cap)
    return partitions.map { partition ->
        // For each partition, produce a copy of [this] with newly assigned variables
        val (a, i) = this.fillSpots(nullary, partitionToMap(partition.toList()))
        if (i <= spots) throw Exception("Didn't assign all variables new names!")
        a
    }.toSet()
}

fun Assignment.fillSpots(nullary: Map<String, Boolean>, indexToPartition: Map<Int, Int>): Pair<Assignment, Int> {
    var i = 1
    return Pair(this.mapValues { (n, t) ->
        if (nullary[n]!!) t else {
            val (newt, newi) = t.fillSpots(indexToPartition, i)
            i = newi
            newt
        }
    }, i)
}

/**
 * @returns Resultant type and next index to fill
 */
fun Type.fillSpots(indexToPartition: Map<Int, Int>, startingIndex: Int): Pair<Type, Int> {
    return when (this) {
        is Error -> throw Exception("This should never happen")
        is Function -> {
            val (left, i1) = this.left.fillSpots(indexToPartition, startingIndex)
            val (rite, i2) = this.rite.fillSpots(indexToPartition, i1)
            Pair(Function(left = left, rite = rite), i2)
        }
        is LabelNode -> {
            var i = startingIndex
            val params = this.params.map {
                val (t, iNext) = it.fillSpots(indexToPartition, i)
                i = iNext
                t
            }
            Pair(LabelNode(label = this.label, params = params), i)
        }
        is ChildHole -> Pair(Variable("v${indexToPartition[startingIndex]!!}"), startingIndex + 1)
        is TypeHole -> Pair(this, startingIndex)
        is Variable -> Pair(Variable("v${indexToPartition[startingIndex]!!}"), startingIndex + 1)
    }
}

fun <T> partitionToMap(partition: List<List<T>>): Map<T, Int> {
    val map = mutableMapOf<T, Int>()
    partition.forEachIndexed { i, part ->
        part.forEach { map[it] = i }
    }
    return map
}

/** All partitions of [list] of size up to [k] */
fun <T> partitionList(list: List<T>, k: Int): Set<Set<List<T>>> {
    if (list.isEmpty() || k <= 0) return setOf(emptySet())
    return generatePartitions(list, k).toSet()
}

fun <T> generatePartitions(list: List<T>, k: Int): List<Set<List<T>>> {
    if (list.isEmpty()) return listOf(emptySet())

    val first = list.first()
    val restPartitions = generatePartitions(list.drop(1), k)
    val newPartitions = mutableListOf<Set<List<T>>>()

    for (partition in restPartitions) {
        if (partition.size < k) {
            // Create a new subset for the first element
            newPartitions.add(partition + setOf(listOf(first)))
        }
        // Try adding first to existing subsets
        for (subset in partition) {
            val l = partition.minus(setOf(subset))
            val r = setOf(subset + listOf(first))
            val modifiedPartition = l + r
            newPartitions.add(modifiedPartition)
        }
    }

    return newPartitions
}

fun main() {
    val list = listOf(1, 2, 3, 4, 5, 6)
    val k = 2
    val partitions = partitionList(list, k)

    println("Partitions with at most $k subsets:")
    for (partition in partitions) {
        println(partition)
    }
}
