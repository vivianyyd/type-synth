package test

import util.NewQuery
import util.ScrappyNewOracle
import util.parseNewApp
import util.parseNewExamples

object IdTest {
    /*
     f: int -> int
     a: int
     id: a -> a
     */
    val examples = mapOf(
        "(+ inc)" to "int -> int",
        "(+ id)" to "a -> a",
        "(+ n)" to "int",
        "(+ (inc n))" to "int",
        "(+ (id inc))" to "int -> int",
        "(+ (id n))" to "int",
        "(- (inc id))" to null,
        // 8 contexts from above, 36 if add below since we add option that id output is fn explicitly.
        //   But we can do something clever - try to eliminate those additional 28 contexts by saying,
        //   inc takes V/L, so id can't bc fn since inc takes output of id.
        //   but that's bad! b/c for all we know, id does output a function, and inc should be able to
        //   take function, so inc input is V
        //   This is a constraint... If id outputs fn, inc takes V; if V then we can restrict inc to take L if we want..
        //   Actually we can do better - Using a negative example! They are actually useful even without L, sometimes..
        //   (How to distinguish examples that'll help from those that will mislead us into optimizing for bad stuff?)
        //   If inc takes V then we erroneously accept inc id, so inc has to take L, so id outputs V

        //   We don't have to check all contexts, since many will have the same combination of types
        //   Sometimes we know some types for a, b are incompatible - that's regardless of types of other named stuff
        //      So we can eliminate large swaths of search space at once
        //      We should do things example-driven
        //      Pairwise constraints on what types are compatible - sounds a lot like constraint initial Sketch idea
        "(+ ((id inc) n))" to "int",
        "(+ (inc (id n)))" to "int",
    )

    val query: NewQuery = parseNewExamples(examples.keys)
    val oracle = ScrappyNewOracle(examples.mapKeys { parseNewApp(it.key) })
}