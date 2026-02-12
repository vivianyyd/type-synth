package oneast

import org.junit.jupiter.api.Test
import query.App
import query.Name

class UnificationTest {
    //    2881 [23:13:47.716]  Potential solution: {0=L0[], 1=L0[], compare=V0 -> V0 -> L0[], max=V0
    // -> V0 -> V0, min=V0 -> V0 -> V0}
    //   2882 [23:13:47.716]  Looking for counterexamples
    //   2883 [23:13:47.948]  Adding counterexample ((compare) (max)) (compare)       Posex: true
    /*
    Turns out, ((compare) (max)) (compare) compiles but not ((compare) (max)) because of weak variables
    whatever whatever in ocaml. Basically, you can't generalize the variables in HM. But you can if you
    see the last element, which ocaml cleverly uses. Basically, OCaml's type checker is a little more
    clever and accepts things that are not HM, which we'll never be able to do, so we fail with no soln.
     */
    @Test
    fun `unification`() {
        val context =
            SearchState(
                mapOf("compare" to 0, "max" to 1),
                listOf(
                    Arrow(Variable(0), Arrow(Variable(0), NamedLabel(0, listOf()))),
                    Arrow(Variable(0), Arrow(Variable(0), Variable(0)))
                ),
                listOf(2),
                mapOf(0 to 0)
            )
        val example = App(App(Name("compare"), Name("max")), Name("compare"))
        val unify = OneUnification(context, listOf(example))
        println("We said: ${unify.ok()} but ocamlc says true")

        println(unify.type(Name("compare")))
        println(unify.type(App(Name("compare"), Name("max"))))
        println(unify.type(Name("compare")))
    }
}
