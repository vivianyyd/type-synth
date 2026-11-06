// 0_basics.types, 1_comparison.types, 4_arith.types, 9_unit.types, 19_ref.types

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

// ref's result is a ref of its argument's type, not the argument itself
(ref Unit)
((=) (ref Num) (ref Num))
((=) (ref Str) (ref Str))
((=) (ref true) (ref false))
((=) (ref (ref Num)) (ref (ref Num)))
((=) (ref Num) (ref Str))
((=) (ref Str) (ref true))
((=) (ref true) (ref Char))
((=) (ref Num) Num)
((=) (ref Str) Str)
((=) (ref (ref Num)) (ref Num))

// ! takes a ref and returns its contents
((!) (ref Char))
((!) (ref Unit))
((=) ((!) (ref Char)) Char)
((=) ((!) (ref Unit)) Unit)
((=) ((!) (ref (ref Num))) (ref Num))
((=) ((!) (ref Num)) Str)
((=) ((!) (ref Str)) Num)
((=) ((!) (ref true)) Char)
((=) ((!) (ref (ref Num))) Num)
((!) true)
((!) Char)
((!) Unit)

// := takes a ref and a value of its contents' type, and returns unit
((:=) (ref Char) Char)
((:=) (ref Unit) Unit)
((:=) (ref (ref Str)) (ref Str))
((:=) (ref Num))
((:=) (ref Str))
((=) ((:=) (ref Num) Num) Unit)
((=) ((:=) (ref Str) Str) Unit)
((=) ((:=) (ref Num) Num) (incr (ref Num)))
((=) ((:=) (ref Num) Num) Num)
((=) ((:=) (ref Str) Str) Str)
((=) ((:=) (ref true) true) true)
((:=) Num)
((:=) Str)
((:=) (ref Str) Num)
((:=) (ref true) Num)
((:=) (ref Char) Str)
((:=) (ref (ref Num)) Num)
((:=) (ref (ref Num)) (ref Str))

// incr and decr take an int ref and return unit
((=) (incr (ref Num)) Unit)
((=) (decr (ref Num)) Unit)
((=) (incr (ref Num)) (decr (ref Num)))
((=) (incr (ref Num)) Num)
((=) (decr (ref Num)) Num)
((=) (incr (ref Num)) true)
((=) (decr (ref Num)) Str)
(incr Num)
(decr Num)
(incr Str)
(decr true)
(decr (ref true))
(incr (ref Char))
(decr (ref Char))
(incr (ref (ref Num)))
(decr (ref (ref Num)))
