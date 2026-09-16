package util

/**
 * A growable array of ints, without the boxing of `MutableList<Int>`. [capacity] is only where it
 * starts; it doubles whenever it fills up.
 */
class IntVec(capacity: Int = 16) {
    private var data = IntArray(capacity)

    var size = 0
        private set

    operator fun get(i: Int) = data[i]

    fun add(v: Int) {
        if (size == data.size) data = data.copyOf(size * 2)
        data[size++] = v
    }

    fun add(a: Int, b: Int) {
        add(a)
        add(b)
    }

    fun removeLast() = data[--size]

    fun isEmpty() = size == 0

    fun clear() {
        size = 0
    }
}
