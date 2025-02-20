package enumgen.types

class ArrowSkeleton {
    /*
    TODO How to find HOFs? I think we can't figure it out until later... So we still have to enum fns
        b/c the fn could be result of partial app?
        Or put(partial app) followed by get()

        HOF if the argument is always a function in all examples. Needs to be iterative process?
        Consider f: (a -> b) -> (a -> b) = (a -> b) -> a -> b
          It's actually wrong to prune the last arrow even if the output is never applied, if we see
          something like f(f(g)) where g is always a function. Since we don't always know that g is a function
          for sure yet, it's definitely wrong to prune the last arrow just because it's unused
          For this example we would probably conclude f is a->a; if the argument is always a function
          which type do we prefer?

        Something is only l[a->b] if it's an l[a] with arrow substituted for a. Otherwise
        if there's something like make: a -> b -> l[a->b] and destruct: l[a->b] -> (a->b)
        It's indistinguishable from make: a -> b -> l[a,b] and destruct: l[a,b] -> (a->b)
     */
}
