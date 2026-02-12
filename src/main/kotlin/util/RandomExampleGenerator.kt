package util

import query.App
import query.Example
import query.Name
import kotlin.random.Random

class RandomExampleGenerator(private val names: List<String>) {
    val random = Random.Default

    private fun randExample(bound: Int): Example =
        if (bound < 2 || random.nextBoolean()) randName() else randApp(bound - 1)

    private fun randName(): Name = Name(names.random())

    private fun randApp(bound: Int): App = App(randExample(bound - 1), randExample(bound - 1))

    fun get(bound: Int) = randApp(bound)
}
