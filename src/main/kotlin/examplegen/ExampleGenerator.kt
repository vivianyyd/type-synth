package examplegen

import util.Application
import enumgen.types.*
import enumgen.types.Function

class ExampleGenerator {
    private var name = 0
    private fun freshValue() = "${name++}"

    /**
     * A type is observable as long as it is a function, or
     * it is *not* only ever seen as the output of a function.
     * For now, we unwrap functions to get their arguments, but we don't include results of partial application
     */
    private fun observableTypes(ts: List<Type>): List<Type> {
        /* For each function, the left is observable, and so is the rite if it is a function.
        TODO For now, we will not bother including partial applications, to avoid blowup. So only keep the left
            The result might still include functions since they can be arguments
        For each non-function, it is observable. */
        val obs = mutableListOf<Type>()
        ts.forEach {
            when (it) {
                is Function -> {
                    fun args(f: Function): List<Type> =
                        listOf(f.left) + (if (f.rite is Function) args(f) else listOf())
                    obs.addAll(args(it))
                }
                is Variable, is LabelNode -> obs.add(it)
                is TypeHole, is Error -> throw Exception("no way")
            }
        }
        return obs
    }

    private fun cartesianProduct(set: List<Type>, n: Int): List<List<Type>> {
        TODO()
    }

    private fun inhabitable(ts: List<Type>): List<Type> {
        val inhab = mutableListOf<Type>()

        val (primitives, parameterized) = ts.filterIsInstance<LabelNode>().partition{ it.params.isEmpty() }
        // We arbitrarily choose to explode the labels with max depth 2.
        // define function cartesian product(set, n) to do set^n. this will give all combos of params.
        // then for each label, include all combo assignments to parameters.
        TODO()


//        ts.forEach {
//            when (it) {
//                is Function -> TODO()
//                is LabelNode -> TODO()
//                is Variable -> {}  // No need to explode, since we add primitive concrete types separately
//                is TypeHole, is Error -> throw Exception("what the")
//            }
//        }
    }
    // explode parameterized types into all possible concrete types.
    // functions with parameterized types can already have concrete values, that's ok


    // primitives: all labels with no params
    // all parameterized types cartesian product all primitives
    // every type which is either nullary or an argument to a function

    fun genAll(ts: List<Type>): List<Application> {
        val examples = mutableListOf<Application>()


        // types to make dummies for:
        // first get observable types
        // then explode parameterized types into all possible concrete types,
        //   excluding functions since types of fn values can contain variables!
        // it's just that right now we assume nothing can be l of a, like [].
        // TODO need to use the concretization for below line.
        val values = observableTypes(ts).associateWith { freshValue() }
        examples.addAll(values.values.map { Application(it, null) })

        ts.forEach {

        }
        TODO()
    }
}