package enumgen

/** Assume the type has only Variables of the same name. Replace those and child holes with various paritionings
 * into at most [cap] variables
 *
 * pure function
 * */
fun Type.populateVariables(cap: Int): Set<Type> {
    val spots = this.recursiveNumVars() + this.recursiveNumChildHoles()
    val partitions = partitionList((1..spots).toList(), cap)
    return partitions.map { partition ->

        var ind = 1

        TODO("Iterate through tree, counting current index")
    }.toSet()

    // each spot gets an index and based on partition gets assigned a variable
    // remember each set in a partition corresponds to a variable
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
    val list = listOf(1, 2, 3, 4)
    val k = 3
    val partitions = partitionList(list, k)

    println("Partitions with at most $k subsets:")
    for (partition in partitions) {
        println(partition)
    }
}
