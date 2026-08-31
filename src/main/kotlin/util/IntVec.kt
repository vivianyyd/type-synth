package util

/** A growable array of ints, without the boxing of `MutableList<Int>`. */
class IntVec(capacity: Int = 16) {
    private var data = IntArray(capacity)

    var size = 0
        private set

    operator fun get(i: Int) = data[i]

    operator fun set(i: Int, v: Int) {
        data[i] = v
    }

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

    fun truncate(n: Int) {
        size = n
    }

    fun toIntArray(): IntArray = data.copyOf(size)
}

/** A growable array of longs, without the boxing of `MutableList<Long>`. */
class LongVec(capacity: Int = 64) {
    private var data = LongArray(capacity)

    var size = 0
        private set

    operator fun get(i: Int) = data[i]

    fun add(v: Long) {
        if (size == data.size) data = data.copyOf(size * 2)
        data[size++] = v
    }

    fun removeLast() = data[--size]

    fun truncate(n: Int) {
        size = n
    }
}
