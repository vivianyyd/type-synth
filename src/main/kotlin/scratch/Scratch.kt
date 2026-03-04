package scratch

import util.lazyCartesianProduct

fun main() {
    val map = mapOf(0 to 0, 1 to 0, 2 to 1, 3 to 2)
    val (labels, arities) = map.toList().unzip()
    val out =
        lazyCartesianProduct(arities.map { (0..it).toList() })
            .map { labels.zip(it).toMap() }
            .toList()
    println(out)
}
