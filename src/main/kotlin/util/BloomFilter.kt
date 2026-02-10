package util

import java.security.MessageDigest
import java.util.*
import kotlin.math.abs
import kotlin.math.ln

class BloomFilter<T>(expectedInsertions: Int, falsePositiveRate: Double = 0.01) {
    private val bitSize: Int
    private val numHashFunctions: Int
    private val bits: BitSet
    private val digest = MessageDigest.getInstance("SHA-256")

    init {
        require(expectedInsertions > 0)
        require(falsePositiveRate in 0.0..1.0)

        bitSize = optimalBitSize(expectedInsertions, falsePositiveRate)
        numHashFunctions = optimalHashFunctions(expectedInsertions, bitSize)
        bits = BitSet(bitSize)
    }

    fun add(item: T) {
        val hashes = hash(item)
        for (i in 0 until numHashFunctions) {
            val index = indexFor(hashes, i)
            bits.set(index)
        }
    }

    fun mightContain(item: T): Boolean {
        val hashes = hash(item)
        for (i in 0 until numHashFunctions) {
            val index = indexFor(hashes, i)
            if (!bits.get(index)) return false
        }
        return true
    }

    private fun hash(item: T): ByteArray {
        return digest.digest(item.toString().toByteArray(Charsets.UTF_8))
    }

    private fun indexFor(hash: ByteArray, i: Int): Int {
        val h1 = bytesToInt(hash, 0)
        val h2 = bytesToInt(hash, 4)
        val combined = h1 + i * h2
        return abs(combined % bitSize)
    }

    private fun bytesToInt(bytes: ByteArray, offset: Int): Int {
        var result = 0
        for (i in 0 until 4) {
            result = (result shl 8) or (bytes[offset + i].toInt() and 0xff)
        }
        return result
    }

    private fun optimalBitSize(n: Int, p: Double): Int {
        return (-n * ln(p) / (ln(2.0) * ln(2.0))).toInt()
    }

    private fun optimalHashFunctions(n: Int, m: Int): Int {
        return ((m.toDouble() / n) * ln(2.0)).toInt().coerceAtLeast(1)
    }
}
