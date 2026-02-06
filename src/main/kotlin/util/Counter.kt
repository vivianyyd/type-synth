package util

class Counter(private var ctr: Int = 0) {
    fun ensureGt(min: Int) {
        if (ctr <= min) ctr = min + 1
    }

    fun get() = ctr++

    fun copy() = Counter(ctr)
}
