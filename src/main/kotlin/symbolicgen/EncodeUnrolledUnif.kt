package symbolicgen

class EncodeUnrolledUnif {


    /*
    generator calls for each name (microopt that might be unnecessary: if only one choice, short circuit to directly produce it)

    for each example, hard-code how to unify it:
    order all examples by subexpressions
    TODO what's the most efficient way to memoize computations in sketch?

    type-expr-dummy-name... type-expr-dummy-name
        they are functions that call the generator dummies
    and they call each other for subexpr references

    TODO how to deal with variable bindings?

    CHECK cons 0 []i
        CHECK cons 0
            CHECK cons
            ASSERT cons is ->
            CHECK 0
            ASSERT 0 < cons param type
        ASSERT cons 0 is ->
        CHECK []i
        ASSERT []i < cons 0 param type
     */
}
