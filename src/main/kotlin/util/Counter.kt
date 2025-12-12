package util

class Counter(private var ctr: Int = 0) {
    fun get() = ctr++

    fun copy() = Counter(ctr)
}
