// 0_basics.types, 1_comparison.types, 4_arith.types, 19_ref.types

(ref Num)
(ref Str)
(ref true)
(ref false)
(ref Char)

((!) (ref Num))
((!) (ref Str))
((!) (ref true))

((:=) (ref Num) Num)
((:=) (ref Str) Str)
((:=) (ref true) false)

(incr (ref Num))
(decr (ref Num))

((=) ((!) (ref Num)) Num)
((=) ((!) (ref Str)) Str)
((=) ((!) (ref true)) false)

(succ ((!) (ref Num)))
((+) ((!) (ref Num)) Num)
(ref (ref Num))
((!) (ref (ref Num)))

((:=) (ref Num) Str)
(incr (ref Str))
(incr (ref true))
(decr (ref Str))
((!) Num)
((!) Str)

// ref returns a ref: use in !, :=, incr, decr
((!) (ref (ref Num)))
((!) ((!) (ref (ref Num))))
((:=) (ref (ref Num)) (ref Num))
(incr (ref ((!) (ref Num))))
(decr (ref ((!) (ref Num))))

// ! returns the contents type: use in more operations
(succ ((!) (ref Num)))
(pred ((!) (ref Num)))
((+) ((!) (ref Num)) ((!) (ref Num)))
((-) ((!) (ref Num)) Num)
(( * ) ((!) (ref Num)) Num)
(abs ((!) (ref Num)))
((=) ((!) (ref Num)) ((!) (ref Num)))
((<) ((!) (ref Num)) Num)

// := takes a ref and a value, returns unit: chain with further operations
((:=) (ref Num) (succ ((!) (ref Num))))
((:=) (ref Num) ((+) Num ((!) (ref Num))))
((:=) (ref Num) (abs ((!) (ref Num))))
((:=) (ref true) ((=) ((!) (ref Num)) Num))

// show polymorphism: ref works for any type
((=) ((!) (ref Str)) Str)
((=) ((!) (ref true)) true)
((=) ((!) (ref Char)) Char)

// deeper chains
(ref ((!) (ref Num)))
(ref (succ ((!) (ref Num))))
((!) (ref (succ ((!) (ref Num)))))
((=) ((!) (ref ((!) (ref Num)))) Num)

// invalid chaining
((:=) (ref Num) ((!) (ref Str)))
(incr (ref ((!) (ref Str))))
((+) ((!) (ref Str)) Num)
